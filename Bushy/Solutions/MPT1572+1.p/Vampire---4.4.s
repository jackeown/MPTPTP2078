%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t50_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:44 EDT 2019

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       : 1042 (4730 expanded)
%              Number of leaves         :  251 (1775 expanded)
%              Depth                    :   22
%              Number of atoms          : 3573 (17632 expanded)
%              Number of equality atoms :   25 ( 249 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2930,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f107,f114,f154,f165,f173,f182,f183,f192,f209,f220,f232,f240,f252,f271,f321,f328,f344,f356,f363,f372,f387,f394,f407,f414,f421,f433,f450,f462,f471,f478,f495,f507,f510,f550,f567,f592,f602,f612,f633,f641,f649,f661,f675,f689,f696,f703,f724,f749,f756,f783,f800,f807,f834,f847,f854,f868,f876,f889,f905,f918,f932,f948,f961,f967,f973,f978,f986,f988,f991,f994,f1028,f1051,f1058,f1065,f1095,f1115,f1122,f1136,f1162,f1182,f1204,f1227,f1243,f1250,f1279,f1294,f1329,f1336,f1358,f1360,f1365,f1366,f1367,f1385,f1387,f1394,f1433,f1453,f1472,f1480,f1498,f1509,f1519,f1545,f1558,f1565,f1594,f1625,f1632,f1647,f1654,f1661,f1668,f1675,f1690,f1709,f1726,f1733,f1751,f1753,f1783,f1815,f1828,f1849,f1856,f1881,f1908,f1962,f1979,f1987,f2012,f2028,f2054,f2084,f2097,f2122,f2129,f2145,f2152,f2159,f2172,f2183,f2186,f2196,f2215,f2218,f2219,f2236,f2261,f2274,f2281,f2324,f2335,f2338,f2340,f2343,f2356,f2358,f2360,f2363,f2369,f2371,f2373,f2398,f2409,f2416,f2434,f2445,f2458,f2465,f2487,f2503,f2517,f2536,f2538,f2586,f2593,f2610,f2630,f2647,f2654,f2672,f2674,f2721,f2735,f2736,f2739,f2741,f2743,f2745,f2747,f2749,f2752,f2759,f2761,f2764,f2793,f2816,f2833,f2846,f2859,f2876,f2893,f2899,f2904,f2912,f2914,f2917,f2923,f2929])).

fof(f2929,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_11
    | ~ spl8_12
    | ~ spl8_360
    | ~ spl8_362 ),
    inference(avatar_contradiction_clause,[],[f2928])).

fof(f2928,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_360
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f2927,f99])).

fof(f99,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2927,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_360
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f2926,f106])).

fof(f106,plain,
    ( l1_orders_2(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_2
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2926,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_360
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f2925,f2892])).

fof(f2892,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_362 ),
    inference(avatar_component_clause,[],[f2891])).

fof(f2891,plain,
    ( spl8_362
  <=> r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_362])])).

fof(f2925,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_360 ),
    inference(subsumption_resolution,[],[f2924,f144])).

fof(f144,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl8_11
  <=> ~ r2_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f2924,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_12
    | ~ spl8_360 ),
    inference(subsumption_resolution,[],[f2920,f153])).

fof(f153,plain,
    ( r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl8_12
  <=> r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f2920,plain,
    ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_360 ),
    inference(resolution,[],[f2886,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK4(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK4(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK4(X0,X1,X2))
              | r1_lattice3(X0,X1,sK4(X0,X1,X2)) )
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK4(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK4(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK4(X0,X1,X2))
          | r1_lattice3(X0,X1,sK4(X0,X1,X2)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t48_yellow_0)).

fof(f2886,plain,
    ( r1_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_360 ),
    inference(avatar_component_clause,[],[f2885])).

fof(f2885,plain,
    ( spl8_360
  <=> r1_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_360])])).

fof(f2923,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_11
    | ~ spl8_12
    | ~ spl8_360
    | ~ spl8_362 ),
    inference(avatar_contradiction_clause,[],[f2922])).

fof(f2922,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_360
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f2918,f2892])).

fof(f2918,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_360 ),
    inference(unit_resulting_resolution,[],[f99,f106,f144,f153,f2886,f81])).

fof(f2917,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | spl8_361
    | ~ spl8_362 ),
    inference(avatar_contradiction_clause,[],[f2916])).

fof(f2916,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_361
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f2915,f2892])).

fof(f2915,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_361 ),
    inference(subsumption_resolution,[],[f2910,f191])).

fof(f191,plain,
    ( m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_20
  <=> m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f2910,plain,
    ( ~ m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_361 ),
    inference(resolution,[],[f2883,f374])).

fof(f374,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),X1) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f373,f106])).

fof(f373,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | r1_lattice3(sK2,X0,X1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f78,f99])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t5_yellow_0)).

fof(f2883,plain,
    ( ~ r1_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_361 ),
    inference(avatar_component_clause,[],[f2882])).

fof(f2882,plain,
    ( spl8_361
  <=> ~ r1_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_361])])).

fof(f2914,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | spl8_361
    | ~ spl8_362 ),
    inference(avatar_contradiction_clause,[],[f2913])).

fof(f2913,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_361
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f2907,f2892])).

fof(f2907,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_361 ),
    inference(unit_resulting_resolution,[],[f191,f2883,f374])).

fof(f2912,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | spl8_361
    | ~ spl8_362 ),
    inference(avatar_contradiction_clause,[],[f2911])).

fof(f2911,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_361
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f2909,f2892])).

fof(f2909,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_361 ),
    inference(unit_resulting_resolution,[],[f99,f106,f191,f2883,f78])).

fof(f2904,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_360
    | spl8_363 ),
    inference(avatar_contradiction_clause,[],[f2903])).

fof(f2903,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_360
    | ~ spl8_363 ),
    inference(subsumption_resolution,[],[f2902,f99])).

fof(f2902,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_360
    | ~ spl8_363 ),
    inference(subsumption_resolution,[],[f2901,f106])).

fof(f2901,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_20
    | ~ spl8_360
    | ~ spl8_363 ),
    inference(subsumption_resolution,[],[f2900,f191])).

fof(f2900,plain,
    ( ~ m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_360
    | ~ spl8_363 ),
    inference(subsumption_resolution,[],[f2897,f2889])).

fof(f2889,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_363 ),
    inference(avatar_component_clause,[],[f2888])).

fof(f2888,plain,
    ( spl8_363
  <=> ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_363])])).

fof(f2897,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_360 ),
    inference(resolution,[],[f2886,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2899,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_360
    | spl8_363 ),
    inference(avatar_contradiction_clause,[],[f2898])).

fof(f2898,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_360
    | ~ spl8_363 ),
    inference(subsumption_resolution,[],[f2895,f2889])).

fof(f2895,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20
    | ~ spl8_360 ),
    inference(unit_resulting_resolution,[],[f99,f106,f191,f2886,f77])).

fof(f2893,plain,
    ( spl8_360
    | spl8_362
    | spl8_1
    | ~ spl8_2
    | spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f2775,f152,f143,f105,f98,f2891,f2885])).

fof(f2775,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r1_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f153,f1000])).

fof(f1000,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK2,X0)
        | r1_lattice3(sK2,X0,sK4(sK2,X0,sK3))
        | r1_lattice3(sK2,sK3,sK4(sK2,X0,sK3)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11 ),
    inference(resolution,[],[f144,f400])).

fof(f400,plain,
    ( ! [X0,X1] :
        ( r2_yellow_0(sK2,X1)
        | r1_lattice3(sK2,X1,sK4(sK2,X0,X1))
        | r1_lattice3(sK2,X0,sK4(sK2,X0,X1))
        | ~ r2_yellow_0(sK2,X0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f399,f106])).

fof(f399,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK2,X0)
        | r1_lattice3(sK2,X1,sK4(sK2,X0,X1))
        | r1_lattice3(sK2,X0,sK4(sK2,X0,X1))
        | ~ l1_orders_2(sK2)
        | r2_yellow_0(sK2,X1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f80,f99])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2876,plain,
    ( ~ spl8_359
    | spl8_1
    | ~ spl8_2
    | spl8_11
    | ~ spl8_12
    | spl8_33 ),
    inference(avatar_split_clause,[],[f2770,f263,f152,f143,f105,f98,f2874])).

fof(f2874,plain,
    ( spl8_359
  <=> ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_359])])).

fof(f263,plain,
    ( spl8_33
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f2770,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f144,f153,f1840])).

fof(f1840,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK2,X1)
        | r2_yellow_0(sK2,X0)
        | ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,X1,X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f1839,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t7_boole)).

fof(f1839,plain,
    ( ! [X0,X1] :
        ( r2_yellow_0(sK2,X0)
        | v1_xboole_0(sK4(sK2,X1,X0))
        | ~ r2_yellow_0(sK2,X1)
        | ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,X1,X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f1838,f264])).

fof(f264,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f263])).

fof(f1838,plain,
    ( ! [X0,X1] :
        ( r2_yellow_0(sK2,X0)
        | v1_xboole_0(u1_struct_0(sK2))
        | v1_xboole_0(sK4(sK2,X1,X0))
        | ~ r2_yellow_0(sK2,X1)
        | ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,X1,X0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f1837,f106])).

fof(f1837,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK2)
        | r2_yellow_0(sK2,X0)
        | v1_xboole_0(u1_struct_0(sK2))
        | v1_xboole_0(sK4(sK2,X1,X0))
        | ~ r2_yellow_0(sK2,X1)
        | ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,X1,X0)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f1297,f99])).

fof(f1297,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | v1_xboole_0(u1_struct_0(X0))
      | v1_xboole_0(sK4(X0,X2,X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_hidden(u1_struct_0(X0),sK4(X0,X2,X1)) ) ),
    inference(resolution,[],[f185,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t1_subset)).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X0),sK4(X0,X1,X2))
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | v1_xboole_0(sK4(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(resolution,[],[f79,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f123,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t2_subset)).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f90,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',antisymmetry_r2_hidden)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2859,plain,
    ( ~ spl8_355
    | spl8_356
    | spl8_33
    | ~ spl8_344 ),
    inference(avatar_split_clause,[],[f2797,f2791,f263,f2857,f2851])).

fof(f2851,plain,
    ( spl8_355
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_355])])).

fof(f2857,plain,
    ( spl8_356
  <=> v1_xboole_0(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_356])])).

fof(f2791,plain,
    ( spl8_344
  <=> m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_344])])).

fof(f2797,plain,
    ( v1_xboole_0(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_33
    | ~ spl8_344 ),
    inference(subsumption_resolution,[],[f2796,f264])).

fof(f2796,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_344 ),
    inference(resolution,[],[f2792,f124])).

fof(f2792,plain,
    ( m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_344 ),
    inference(avatar_component_clause,[],[f2791])).

fof(f2846,plain,
    ( ~ spl8_353
    | spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | spl8_33
    | spl8_39 ),
    inference(avatar_split_clause,[],[f2769,f326,f263,f152,f105,f98,f2844])).

fof(f2844,plain,
    ( spl8_353
  <=> ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_353])])).

fof(f326,plain,
    ( spl8_39
  <=> ~ r2_yellow_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f2769,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_33
    | ~ spl8_39 ),
    inference(unit_resulting_resolution,[],[f327,f153,f1840])).

fof(f327,plain,
    ( ~ r2_yellow_0(sK2,k1_xboole_0)
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f326])).

fof(f2833,plain,
    ( spl8_350
    | spl8_33
    | ~ spl8_344 ),
    inference(avatar_split_clause,[],[f2795,f2791,f263,f2831])).

fof(f2831,plain,
    ( spl8_350
  <=> r2_hidden(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_350])])).

fof(f2795,plain,
    ( r2_hidden(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_344 ),
    inference(unit_resulting_resolution,[],[f264,f2792,f90])).

fof(f2816,plain,
    ( ~ spl8_347
    | spl8_348
    | ~ spl8_20
    | spl8_33 ),
    inference(avatar_split_clause,[],[f2786,f263,f190,f2814,f2808])).

fof(f2808,plain,
    ( spl8_347
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_347])])).

fof(f2814,plain,
    ( spl8_348
  <=> v1_xboole_0(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_348])])).

fof(f2786,plain,
    ( v1_xboole_0(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_20
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f2785,f264])).

fof(f2785,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_20 ),
    inference(resolution,[],[f191,f124])).

fof(f2793,plain,
    ( spl8_344
    | spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | spl8_39 ),
    inference(avatar_split_clause,[],[f2771,f326,f152,f105,f98,f2791])).

fof(f2771,plain,
    ( m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_39 ),
    inference(unit_resulting_resolution,[],[f99,f106,f327,f153,f79])).

fof(f2764,plain,
    ( ~ spl8_20
    | spl8_29
    | spl8_33 ),
    inference(avatar_contradiction_clause,[],[f2763])).

fof(f2763,plain,
    ( $false
    | ~ spl8_20
    | ~ spl8_29
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f191,f2762])).

fof(f2762,plain,
    ( ~ m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_29
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f738,f264])).

fof(f738,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_29 ),
    inference(resolution,[],[f239,f90])).

fof(f239,plain,
    ( ~ r2_hidden(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl8_29
  <=> ~ r2_hidden(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f2761,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f2760])).

fof(f2760,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2374,f2757])).

fof(f2757,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2708,f2468])).

fof(f2468,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,X0,sK5(sK2,sK3,X0))
        | r1_yellow_0(sK2,X0)
        | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2467,f2388])).

fof(f2388,plain,
    ( ! [X2] :
        ( m1_subset_1(sK5(sK2,sK3,X2),u1_struct_0(sK2))
        | r1_yellow_0(sK2,X2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2387,f99])).

fof(f2387,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK2,X2)
        | m1_subset_1(sK5(sK2,sK3,X2),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2382,f106])).

fof(f2382,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK2,X2)
        | m1_subset_1(sK5(sK2,sK3,X2),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_14 ),
    inference(resolution,[],[f161,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK5(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK5(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK5(X0,X1,X2))
              | r2_lattice3(X0,X1,sK5(X0,X1,X2)) )
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK5(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK5(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK5(X0,X1,X2))
          | r2_lattice3(X0,X1,sK5(X0,X1,X2)) )
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t46_yellow_0)).

fof(f161,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_14
  <=> r1_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f2467,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,X0,sK5(sK2,sK3,X0))
        | r1_yellow_0(sK2,X0)
        | ~ m1_subset_1(sK5(sK2,sK3,X0),u1_struct_0(sK2))
        | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(resolution,[],[f2384,f255])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),X1) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f254,f106])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | r2_lattice3(sK2,X0,X1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f76,f99])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2384,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
        | ~ r2_lattice3(sK2,X0,sK5(sK2,sK3,X0))
        | r1_yellow_0(sK2,X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2383,f99])).

fof(f2383,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | ~ r2_lattice3(sK2,X0,sK5(sK2,sK3,X0))
        | ~ r2_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
        | v2_struct_0(sK2) )
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2380,f106])).

fof(f2380,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | ~ r2_lattice3(sK2,X0,sK5(sK2,sK3,X0))
        | ~ r2_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_14 ),
    inference(resolution,[],[f161,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2708,plain,
    ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(factoring,[],[f2510])).

fof(f2510,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,sK3,X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,X1)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2509,f2388])).

fof(f2509,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,sK3,X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,X1))
        | ~ m1_subset_1(sK5(sK2,sK3,X1),u1_struct_0(sK2)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2508,f99])).

fof(f2508,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,sK3,X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,X1))
        | ~ m1_subset_1(sK5(sK2,sK3,X1),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2505,f106])).

fof(f2505,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,sK3,X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,X1))
        | ~ m1_subset_1(sK5(sK2,sK3,X1),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(resolution,[],[f2386,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2386,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,sK3,sK5(sK2,sK3,X1))
        | r2_lattice3(sK2,X1,sK5(sK2,sK3,X1))
        | r1_yellow_0(sK2,X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2385,f99])).

fof(f2385,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,X1,sK5(sK2,sK3,X1))
        | r2_lattice3(sK2,sK3,sK5(sK2,sK3,X1))
        | v2_struct_0(sK2) )
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2381,f106])).

fof(f2381,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,X1,sK5(sK2,sK3,X1))
        | r2_lattice3(sK2,sK3,sK5(sK2,sK3,X1))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_14 ),
    inference(resolution,[],[f161,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,sK5(X0,X1,X2))
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2374,plain,
    ( ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f135,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
        & r1_yellow_0(X0,X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
        & r1_yellow_0(X0,X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f135,plain,
    ( sP0(sK2,sK3)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_6
  <=> sP0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2759,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f2758])).

fof(f2758,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f2376,f2757])).

fof(f2376,plain,
    ( ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_6 ),
    inference(resolution,[],[f135,f66])).

fof(f2752,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2751])).

fof(f2751,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(subsumption_resolution,[],[f2750,f2720])).

fof(f2720,plain,
    ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_342 ),
    inference(avatar_component_clause,[],[f2719])).

fof(f2719,plain,
    ( spl8_342
  <=> r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_342])])).

fof(f2750,plain,
    ( ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(subsumption_resolution,[],[f2733,f169])).

fof(f169,plain,
    ( ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl8_17
  <=> ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f2733,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_342 ),
    inference(resolution,[],[f2720,f2468])).

fof(f2749,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2748])).

fof(f2748,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(subsumption_resolution,[],[f2722,f2720])).

fof(f2722,plain,
    ( ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f169,f2720,f2468])).

fof(f2747,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2746])).

fof(f2746,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(subsumption_resolution,[],[f2723,f169])).

fof(f2723,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f2720,f2720,f2468])).

fof(f2745,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2744])).

fof(f2744,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(subsumption_resolution,[],[f2726,f2720])).

fof(f2726,plain,
    ( ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f169,f2720,f2468])).

fof(f2743,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2742])).

fof(f2742,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(subsumption_resolution,[],[f2727,f169])).

fof(f2727,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f2720,f2720,f2468])).

fof(f2741,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_314
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2740])).

fof(f2740,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_314
    | ~ spl8_342 ),
    inference(subsumption_resolution,[],[f2729,f2731])).

fof(f2731,plain,
    ( r2_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_314
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f99,f106,f2444,f2720,f76])).

fof(f2444,plain,
    ( m1_subset_1(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_314 ),
    inference(avatar_component_clause,[],[f2443])).

fof(f2443,plain,
    ( spl8_314
  <=> m1_subset_1(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_314])])).

fof(f2729,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f169,f2720,f2384])).

fof(f2739,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_314
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2738])).

fof(f2738,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_314
    | ~ spl8_342 ),
    inference(subsumption_resolution,[],[f2730,f2731])).

fof(f2730,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f99,f106,f161,f169,f2720,f84])).

fof(f2736,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2728])).

fof(f2728,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f169,f2720,f2720,f2468])).

fof(f2735,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17
    | ~ spl8_342 ),
    inference(avatar_contradiction_clause,[],[f2724])).

fof(f2724,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17
    | ~ spl8_342 ),
    inference(unit_resulting_resolution,[],[f169,f2720,f2720,f2468])).

fof(f2721,plain,
    ( spl8_342
    | spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17 ),
    inference(avatar_split_clause,[],[f2714,f168,f160,f105,f98,f2719])).

fof(f2714,plain,
    ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f2708,f169])).

fof(f2674,plain,
    ( spl8_113
    | ~ spl8_318
    | ~ spl8_334 ),
    inference(avatar_contradiction_clause,[],[f2673])).

fof(f2673,plain,
    ( $false
    | ~ spl8_113
    | ~ spl8_318
    | ~ spl8_334 ),
    inference(subsumption_resolution,[],[f2666,f830])).

fof(f830,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_113 ),
    inference(avatar_component_clause,[],[f829])).

fof(f829,plain,
    ( spl8_113
  <=> ~ r2_hidden(k1_xboole_0,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f2666,plain,
    ( r2_hidden(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_318
    | ~ spl8_334 ),
    inference(backward_demodulation,[],[f2660,f2464])).

fof(f2464,plain,
    ( r2_hidden(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_318 ),
    inference(avatar_component_clause,[],[f2463])).

fof(f2463,plain,
    ( spl8_318
  <=> r2_hidden(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_318])])).

fof(f2660,plain,
    ( k1_xboole_0 = sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_334 ),
    inference(unit_resulting_resolution,[],[f2609,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t6_boole)).

fof(f2609,plain,
    ( v1_xboole_0(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_334 ),
    inference(avatar_component_clause,[],[f2608])).

fof(f2608,plain,
    ( spl8_334
  <=> v1_xboole_0(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_334])])).

fof(f2672,plain,
    ( spl8_117
    | ~ spl8_314
    | ~ spl8_334 ),
    inference(avatar_contradiction_clause,[],[f2671])).

fof(f2671,plain,
    ( $false
    | ~ spl8_117
    | ~ spl8_314
    | ~ spl8_334 ),
    inference(subsumption_resolution,[],[f2664,f850])).

fof(f850,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_117 ),
    inference(avatar_component_clause,[],[f849])).

fof(f849,plain,
    ( spl8_117
  <=> ~ m1_subset_1(k1_xboole_0,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f2664,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_314
    | ~ spl8_334 ),
    inference(backward_demodulation,[],[f2660,f2444])).

fof(f2654,plain,
    ( spl8_340
    | spl8_335 ),
    inference(avatar_split_clause,[],[f2617,f2605,f2652])).

fof(f2652,plain,
    ( spl8_340
  <=> r2_hidden(sK6(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_340])])).

fof(f2605,plain,
    ( spl8_335
  <=> ~ v1_xboole_0(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_335])])).

fof(f2617,plain,
    ( r2_hidden(sK6(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_335 ),
    inference(unit_resulting_resolution,[],[f85,f2606,f90])).

fof(f2606,plain,
    ( ~ v1_xboole_0(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_335 ),
    inference(avatar_component_clause,[],[f2605])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',existence_m1_subset_1)).

fof(f2647,plain,
    ( ~ spl8_339
    | spl8_335 ),
    inference(avatar_split_clause,[],[f2616,f2605,f2645])).

fof(f2645,plain,
    ( spl8_339
  <=> ~ r2_hidden(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),sK6(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_339])])).

fof(f2616,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),sK6(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))))
    | ~ spl8_335 ),
    inference(unit_resulting_resolution,[],[f85,f2606,f123])).

fof(f2630,plain,
    ( spl8_336
    | spl8_33
    | ~ spl8_328 ),
    inference(avatar_split_clause,[],[f2595,f2584,f263,f2628])).

fof(f2628,plain,
    ( spl8_336
  <=> r2_hidden(sK5(sK2,sK3,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_336])])).

fof(f2584,plain,
    ( spl8_328
  <=> m1_subset_1(sK5(sK2,sK3,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_328])])).

fof(f2595,plain,
    ( r2_hidden(sK5(sK2,sK3,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_328 ),
    inference(unit_resulting_resolution,[],[f264,f2585,f90])).

fof(f2585,plain,
    ( m1_subset_1(sK5(sK2,sK3,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))),u1_struct_0(sK2))
    | ~ spl8_328 ),
    inference(avatar_component_clause,[],[f2584])).

fof(f2610,plain,
    ( ~ spl8_333
    | spl8_334
    | spl8_33
    | ~ spl8_314 ),
    inference(avatar_split_clause,[],[f2449,f2443,f263,f2608,f2602])).

fof(f2602,plain,
    ( spl8_333
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_333])])).

fof(f2449,plain,
    ( v1_xboole_0(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_33
    | ~ spl8_314 ),
    inference(subsumption_resolution,[],[f2448,f264])).

fof(f2448,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_314 ),
    inference(resolution,[],[f2444,f124])).

fof(f2593,plain,
    ( ~ spl8_331
    | ~ spl8_34
    | spl8_191 ),
    inference(avatar_split_clause,[],[f2577,f1448,f269,f2591])).

fof(f2591,plain,
    ( spl8_331
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,sK3,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_331])])).

fof(f269,plain,
    ( spl8_34
  <=> ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,X0))
        | v1_xboole_0(sK5(sK2,sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f1448,plain,
    ( spl8_191
  <=> ~ r1_yellow_0(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_191])])).

fof(f2577,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,sK3,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))))
    | ~ spl8_34
    | ~ spl8_191 ),
    inference(unit_resulting_resolution,[],[f1449,f2574])).

fof(f2574,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,sK3,X0))
        | r1_yellow_0(sK2,X0) )
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f2573,f92])).

fof(f2573,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | v1_xboole_0(sK5(sK2,sK3,X0))
        | ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,sK3,X0)) )
    | ~ spl8_34 ),
    inference(resolution,[],[f270,f89])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,X0))
        | r1_yellow_0(sK2,X0)
        | v1_xboole_0(sK5(sK2,sK3,X0)) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f269])).

fof(f1449,plain,
    ( ~ r1_yellow_0(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_191 ),
    inference(avatar_component_clause,[],[f1448])).

fof(f2586,plain,
    ( spl8_328
    | spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_191 ),
    inference(avatar_split_clause,[],[f2426,f1448,f160,f105,f98,f2584])).

fof(f2426,plain,
    ( m1_subset_1(sK5(sK2,sK3,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_191 ),
    inference(unit_resulting_resolution,[],[f99,f106,f161,f1449,f82])).

fof(f2538,plain,
    ( spl8_113
    | ~ spl8_310
    | ~ spl8_322 ),
    inference(avatar_contradiction_clause,[],[f2537])).

fof(f2537,plain,
    ( $false
    | ~ spl8_113
    | ~ spl8_310
    | ~ spl8_322 ),
    inference(subsumption_resolution,[],[f2530,f830])).

fof(f2530,plain,
    ( r2_hidden(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_310
    | ~ spl8_322 ),
    inference(backward_demodulation,[],[f2523,f2415])).

fof(f2415,plain,
    ( r2_hidden(sK5(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_310 ),
    inference(avatar_component_clause,[],[f2414])).

fof(f2414,plain,
    ( spl8_310
  <=> r2_hidden(sK5(sK2,sK3,k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_310])])).

fof(f2523,plain,
    ( k1_xboole_0 = sK5(sK2,sK3,k1_xboole_0)
    | ~ spl8_322 ),
    inference(unit_resulting_resolution,[],[f2486,f74])).

fof(f2486,plain,
    ( v1_xboole_0(sK5(sK2,sK3,k1_xboole_0))
    | ~ spl8_322 ),
    inference(avatar_component_clause,[],[f2485])).

fof(f2485,plain,
    ( spl8_322
  <=> v1_xboole_0(sK5(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_322])])).

fof(f2536,plain,
    ( spl8_117
    | ~ spl8_306
    | ~ spl8_322 ),
    inference(avatar_contradiction_clause,[],[f2535])).

fof(f2535,plain,
    ( $false
    | ~ spl8_117
    | ~ spl8_306
    | ~ spl8_322 ),
    inference(subsumption_resolution,[],[f2528,f850])).

fof(f2528,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_306
    | ~ spl8_322 ),
    inference(backward_demodulation,[],[f2523,f2397])).

fof(f2397,plain,
    ( m1_subset_1(sK5(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_306 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f2396,plain,
    ( spl8_306
  <=> m1_subset_1(sK5(sK2,sK3,k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_306])])).

fof(f2517,plain,
    ( spl8_326
    | spl8_323 ),
    inference(avatar_split_clause,[],[f2493,f2482,f2515])).

fof(f2515,plain,
    ( spl8_326
  <=> r2_hidden(sK6(sK5(sK2,sK3,k1_xboole_0)),sK5(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_326])])).

fof(f2482,plain,
    ( spl8_323
  <=> ~ v1_xboole_0(sK5(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_323])])).

fof(f2493,plain,
    ( r2_hidden(sK6(sK5(sK2,sK3,k1_xboole_0)),sK5(sK2,sK3,k1_xboole_0))
    | ~ spl8_323 ),
    inference(unit_resulting_resolution,[],[f85,f2483,f90])).

fof(f2483,plain,
    ( ~ v1_xboole_0(sK5(sK2,sK3,k1_xboole_0))
    | ~ spl8_323 ),
    inference(avatar_component_clause,[],[f2482])).

fof(f2503,plain,
    ( ~ spl8_325
    | spl8_323 ),
    inference(avatar_split_clause,[],[f2492,f2482,f2501])).

fof(f2501,plain,
    ( spl8_325
  <=> ~ r2_hidden(sK5(sK2,sK3,k1_xboole_0),sK6(sK5(sK2,sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_325])])).

fof(f2492,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,k1_xboole_0),sK6(sK5(sK2,sK3,k1_xboole_0)))
    | ~ spl8_323 ),
    inference(unit_resulting_resolution,[],[f85,f2483,f123])).

fof(f2487,plain,
    ( ~ spl8_321
    | spl8_322
    | spl8_33
    | ~ spl8_306 ),
    inference(avatar_split_clause,[],[f2402,f2396,f263,f2485,f2479])).

fof(f2479,plain,
    ( spl8_321
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_321])])).

fof(f2402,plain,
    ( v1_xboole_0(sK5(sK2,sK3,k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,k1_xboole_0))
    | ~ spl8_33
    | ~ spl8_306 ),
    inference(subsumption_resolution,[],[f2401,f264])).

fof(f2401,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK5(sK2,sK3,k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,k1_xboole_0))
    | ~ spl8_306 ),
    inference(resolution,[],[f2397,f124])).

fof(f2465,plain,
    ( spl8_318
    | spl8_33
    | ~ spl8_314 ),
    inference(avatar_split_clause,[],[f2447,f2443,f263,f2463])).

fof(f2447,plain,
    ( r2_hidden(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_314 ),
    inference(unit_resulting_resolution,[],[f264,f2444,f90])).

fof(f2458,plain,
    ( ~ spl8_317
    | spl8_33
    | ~ spl8_314 ),
    inference(avatar_split_clause,[],[f2446,f2443,f263,f2456])).

fof(f2456,plain,
    ( spl8_317
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_317])])).

fof(f2446,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_33
    | ~ spl8_314 ),
    inference(unit_resulting_resolution,[],[f264,f2444,f123])).

fof(f2445,plain,
    ( spl8_314
    | spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_17 ),
    inference(avatar_split_clause,[],[f2390,f168,f160,f105,f98,f2443])).

fof(f2390,plain,
    ( m1_subset_1(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f99,f106,f161,f169,f82])).

fof(f2434,plain,
    ( ~ spl8_313
    | spl8_191 ),
    inference(avatar_split_clause,[],[f2427,f1448,f2432])).

fof(f2432,plain,
    ( spl8_313
  <=> ~ sP0(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_313])])).

fof(f2427,plain,
    ( ~ sP0(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_191 ),
    inference(unit_resulting_resolution,[],[f1449,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2416,plain,
    ( spl8_310
    | spl8_33
    | ~ spl8_306 ),
    inference(avatar_split_clause,[],[f2400,f2396,f263,f2414])).

fof(f2400,plain,
    ( r2_hidden(sK5(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_306 ),
    inference(unit_resulting_resolution,[],[f264,f2397,f90])).

fof(f2409,plain,
    ( ~ spl8_309
    | spl8_33
    | ~ spl8_306 ),
    inference(avatar_split_clause,[],[f2399,f2396,f263,f2407])).

fof(f2407,plain,
    ( spl8_309
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_309])])).

fof(f2399,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,sK3,k1_xboole_0))
    | ~ spl8_33
    | ~ spl8_306 ),
    inference(unit_resulting_resolution,[],[f264,f2397,f123])).

fof(f2398,plain,
    ( spl8_306
    | spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | spl8_41 ),
    inference(avatar_split_clause,[],[f2378,f339,f160,f105,f98,f2396])).

fof(f339,plain,
    ( spl8_41
  <=> ~ r1_yellow_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f2378,plain,
    ( m1_subset_1(sK5(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f99,f106,f340,f161,f82])).

fof(f340,plain,
    ( ~ r1_yellow_0(sK2,k1_xboole_0)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f339])).

fof(f2373,plain,
    ( ~ spl8_6
    | spl8_15 ),
    inference(avatar_contradiction_clause,[],[f2372])).

fof(f2372,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f135,f422])).

fof(f422,plain,
    ( ~ sP0(sK2,sK3)
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f164,f65])).

fof(f164,plain,
    ( ~ r1_yellow_0(sK2,sK3)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_15
  <=> ~ r1_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f2371,plain,
    ( spl8_215
    | ~ spl8_224 ),
    inference(avatar_contradiction_clause,[],[f2370])).

fof(f2370,plain,
    ( $false
    | ~ spl8_215
    | ~ spl8_224 ),
    inference(subsumption_resolution,[],[f1628,f1691])).

fof(f1691,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2))
    | ~ spl8_224 ),
    inference(unit_resulting_resolution,[],[f1674,f89])).

fof(f1674,plain,
    ( r2_hidden(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2))
    | ~ spl8_224 ),
    inference(avatar_component_clause,[],[f1673])).

fof(f1673,plain,
    ( spl8_224
  <=> r2_hidden(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_224])])).

fof(f1628,plain,
    ( ~ m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2))
    | ~ spl8_215 ),
    inference(avatar_component_clause,[],[f1627])).

fof(f1627,plain,
    ( spl8_215
  <=> ~ m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_215])])).

fof(f2369,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302
    | spl8_305 ),
    inference(avatar_contradiction_clause,[],[f2368])).

fof(f2368,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302
    | ~ spl8_305 ),
    inference(subsumption_resolution,[],[f2367,f2323])).

fof(f2323,plain,
    ( ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_305 ),
    inference(avatar_component_clause,[],[f2322])).

fof(f2322,plain,
    ( spl8_305
  <=> ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_305])])).

fof(f2367,plain,
    ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(forward_demodulation,[],[f2366,f87])).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',commutativity_k3_xboole_0)).

fof(f2366,plain,
    ( r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(subsumption_resolution,[],[f2365,f99])).

fof(f2365,plain,
    ( r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(subsumption_resolution,[],[f2364,f106])).

fof(f2364,plain,
    ( r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(subsumption_resolution,[],[f2353,f219])).

fof(f219,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl8_24
  <=> m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f2353,plain,
    ( r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_302 ),
    inference(resolution,[],[f2314,f75])).

fof(f2314,plain,
    ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_302 ),
    inference(avatar_component_clause,[],[f2313])).

fof(f2313,plain,
    ( spl8_302
  <=> r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_302])])).

fof(f2363,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(avatar_contradiction_clause,[],[f2362])).

fof(f2362,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(subsumption_resolution,[],[f2361,f164])).

fof(f2361,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(subsumption_resolution,[],[f2352,f2350])).

fof(f2350,plain,
    ( r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(unit_resulting_resolution,[],[f99,f106,f219,f2314,f76])).

fof(f2352,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r1_yellow_0(sK2,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_302 ),
    inference(resolution,[],[f2314,f1009])).

fof(f1009,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | ~ r2_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | r1_yellow_0(sK2,X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1008,f99])).

fof(f1008,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | ~ r2_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | v2_struct_0(sK2) )
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1005,f106])).

fof(f1005,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | ~ r2_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_16 ),
    inference(resolution,[],[f172,f84])).

fof(f172,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl8_16
  <=> r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f2360,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(avatar_contradiction_clause,[],[f2359])).

fof(f2359,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(subsumption_resolution,[],[f2346,f2350])).

fof(f2346,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_302 ),
    inference(unit_resulting_resolution,[],[f164,f2314,f1009])).

fof(f2358,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(avatar_contradiction_clause,[],[f2357])).

fof(f2357,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(subsumption_resolution,[],[f2349,f2350])).

fof(f2349,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_302 ),
    inference(unit_resulting_resolution,[],[f99,f106,f164,f172,f2314,f84])).

fof(f2356,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302
    | spl8_305 ),
    inference(avatar_contradiction_clause,[],[f2355])).

fof(f2355,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302
    | ~ spl8_305 ),
    inference(subsumption_resolution,[],[f2354,f2323])).

fof(f2354,plain,
    ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(forward_demodulation,[],[f2351,f87])).

fof(f2351,plain,
    ( r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_302 ),
    inference(unit_resulting_resolution,[],[f99,f106,f219,f2314,f75])).

fof(f2343,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | spl8_303 ),
    inference(avatar_contradiction_clause,[],[f2342])).

fof(f2342,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_303 ),
    inference(subsumption_resolution,[],[f2341,f164])).

fof(f2341,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_303 ),
    inference(subsumption_resolution,[],[f2331,f2329])).

fof(f2329,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_303 ),
    inference(unit_resulting_resolution,[],[f99,f106,f219,f2317,f75])).

fof(f2317,plain,
    ( ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_303 ),
    inference(avatar_component_clause,[],[f2316])).

fof(f2316,plain,
    ( spl8_303
  <=> ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_303])])).

fof(f2331,plain,
    ( r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r1_yellow_0(sK2,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_303 ),
    inference(resolution,[],[f2317,f1011])).

fof(f1011,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r2_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1010,f99])).

fof(f1010,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | v2_struct_0(sK2) )
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1006,f106])).

fof(f1006,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_16 ),
    inference(resolution,[],[f172,f83])).

fof(f2340,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | spl8_303 ),
    inference(avatar_contradiction_clause,[],[f2339])).

fof(f2339,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_303 ),
    inference(subsumption_resolution,[],[f2325,f2329])).

fof(f2325,plain,
    ( r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_303 ),
    inference(unit_resulting_resolution,[],[f164,f2317,f1011])).

fof(f2338,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16
    | spl8_303
    | spl8_305 ),
    inference(avatar_contradiction_clause,[],[f2337])).

fof(f2337,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_303
    | ~ spl8_305 ),
    inference(subsumption_resolution,[],[f2326,f2323])).

fof(f2326,plain,
    ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_303 ),
    inference(unit_resulting_resolution,[],[f164,f2317,f1442])).

fof(f1442,plain,
    ( ! [X1] :
        ( r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r2_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1441,f1013])).

fof(f1013,plain,
    ( ! [X2] :
        ( m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2),u1_struct_0(sK2))
        | r1_yellow_0(sK2,X2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1012,f99])).

fof(f1012,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK2,X2)
        | m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1007,f106])).

fof(f1007,plain,
    ( ! [X2] :
        ( r1_yellow_0(sK2,X2)
        | m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_16 ),
    inference(resolution,[],[f172,f82])).

fof(f1441,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1440,f99])).

fof(f1440,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1436,f106])).

fof(f1436,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(resolution,[],[f1144,f75])).

fof(f1144,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1143,f87])).

fof(f1143,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1142,f1013])).

fof(f1142,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1141,f99])).

fof(f1141,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1138,f106])).

fof(f1138,plain,
    ( ! [X1] :
        ( r2_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | r1_yellow_0(sK2,X1)
        | r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
        | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(resolution,[],[f1011,f75])).

fof(f2335,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | spl8_303 ),
    inference(avatar_contradiction_clause,[],[f2334])).

fof(f2334,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_24
    | ~ spl8_303 ),
    inference(subsumption_resolution,[],[f2328,f2329])).

fof(f2328,plain,
    ( r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_303 ),
    inference(unit_resulting_resolution,[],[f99,f106,f164,f172,f2317,f83])).

fof(f2324,plain,
    ( ~ spl8_303
    | ~ spl8_305
    | spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f1882,f171,f163,f105,f98,f2322,f2316])).

fof(f1882,plain,
    ( ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(resolution,[],[f1319,f164])).

fof(f1319,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | ~ r2_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1316,f1013])).

fof(f1316,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | r1_yellow_0(sK2,X0)
        | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0),u1_struct_0(sK2))
        | ~ r2_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(resolution,[],[f1108,f255])).

fof(f1108,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | r1_yellow_0(sK2,X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f1107,f87])).

fof(f1107,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | r1_yellow_0(sK2,X0)
        | ~ r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1106,f1013])).

fof(f1106,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
        | r1_yellow_0(sK2,X0)
        | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0),u1_struct_0(sK2))
        | ~ r2_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(resolution,[],[f1009,f255])).

fof(f2281,plain,
    ( spl8_300
    | ~ spl8_296 ),
    inference(avatar_split_clause,[],[f2262,f2259,f2279])).

fof(f2279,plain,
    ( spl8_300
  <=> m1_subset_1(k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_300])])).

fof(f2259,plain,
    ( spl8_296
  <=> r2_hidden(k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_296])])).

fof(f2262,plain,
    ( m1_subset_1(k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_296 ),
    inference(unit_resulting_resolution,[],[f2260,f89])).

fof(f2260,plain,
    ( r2_hidden(k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_296 ),
    inference(avatar_component_clause,[],[f2259])).

fof(f2274,plain,
    ( ~ spl8_299
    | spl8_273
    | ~ spl8_274 ),
    inference(avatar_split_clause,[],[f2249,f2095,f2089,f2272])).

fof(f2272,plain,
    ( spl8_299
  <=> ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_299])])).

fof(f2089,plain,
    ( spl8_273
  <=> ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_273])])).

fof(f2095,plain,
    ( spl8_274
  <=> v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_274])])).

fof(f2249,plain,
    ( ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),k1_xboole_0)
    | ~ spl8_273
    | ~ spl8_274 ),
    inference(backward_demodulation,[],[f2242,f2090])).

fof(f2090,plain,
    ( ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))
    | ~ spl8_273 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2242,plain,
    ( k1_xboole_0 = sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_274 ),
    inference(unit_resulting_resolution,[],[f2096,f74])).

fof(f2096,plain,
    ( v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))
    | ~ spl8_274 ),
    inference(avatar_component_clause,[],[f2095])).

fof(f2261,plain,
    ( spl8_296
    | ~ spl8_234
    | ~ spl8_274 ),
    inference(avatar_split_clause,[],[f2250,f2095,f1731,f2259])).

fof(f1731,plain,
    ( spl8_234
  <=> r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_234])])).

fof(f2250,plain,
    ( r2_hidden(k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_234
    | ~ spl8_274 ),
    inference(backward_demodulation,[],[f2242,f1732])).

fof(f1732,plain,
    ( r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_234 ),
    inference(avatar_component_clause,[],[f1731])).

fof(f2236,plain,
    ( spl8_294
    | spl8_275 ),
    inference(avatar_split_clause,[],[f2112,f2092,f2234])).

fof(f2234,plain,
    ( spl8_294
  <=> r2_hidden(sK6(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_294])])).

fof(f2092,plain,
    ( spl8_275
  <=> ~ v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_275])])).

fof(f2112,plain,
    ( r2_hidden(sK6(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))
    | ~ spl8_275 ),
    inference(unit_resulting_resolution,[],[f85,f2093,f90])).

fof(f2093,plain,
    ( ~ v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))
    | ~ spl8_275 ),
    inference(avatar_component_clause,[],[f2092])).

fof(f2219,plain,
    ( spl8_286
    | spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | spl8_41
    | spl8_289 ),
    inference(avatar_split_clause,[],[f2189,f2170,f339,f171,f105,f98,f2161])).

fof(f2161,plain,
    ( spl8_286
  <=> r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_286])])).

fof(f2170,plain,
    ( spl8_289
  <=> ~ r2_lattice3(sK2,k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_289])])).

fof(f2189,plain,
    ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41
    | ~ spl8_289 ),
    inference(subsumption_resolution,[],[f2178,f340])).

fof(f2178,plain,
    ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | r1_yellow_0(sK2,k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_289 ),
    inference(resolution,[],[f2171,f1144])).

fof(f2171,plain,
    ( ~ r2_lattice3(sK2,k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_289 ),
    inference(avatar_component_clause,[],[f2170])).

fof(f2218,plain,
    ( spl8_286
    | spl8_288
    | spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | spl8_41 ),
    inference(avatar_split_clause,[],[f1918,f339,f171,f105,f98,f2167,f2161])).

fof(f2167,plain,
    ( spl8_288
  <=> r2_lattice3(sK2,k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_288])])).

fof(f1918,plain,
    ( r2_lattice3(sK2,k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41 ),
    inference(forward_demodulation,[],[f1914,f115])).

fof(f115,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[],[f87,f73])).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t2_boole)).

fof(f1914,plain,
    ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | r2_lattice3(sK2,k3_xboole_0(k1_xboole_0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41 ),
    inference(resolution,[],[f1442,f340])).

fof(f2215,plain,
    ( spl8_292
    | spl8_1
    | ~ spl8_2
    | ~ spl8_140
    | ~ spl8_290 ),
    inference(avatar_split_clause,[],[f2200,f2194,f1026,f105,f98,f2213])).

fof(f2213,plain,
    ( spl8_292
  <=> r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_292])])).

fof(f1026,plain,
    ( spl8_140
  <=> m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).

fof(f2194,plain,
    ( spl8_290
  <=> r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_290])])).

fof(f2200,plain,
    ( r2_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_140
    | ~ spl8_290 ),
    inference(unit_resulting_resolution,[],[f99,f106,f1027,f2195,f76])).

fof(f2195,plain,
    ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_290 ),
    inference(avatar_component_clause,[],[f2194])).

fof(f1027,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_140 ),
    inference(avatar_component_clause,[],[f1026])).

fof(f2196,plain,
    ( spl8_290
    | spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | spl8_41
    | spl8_289 ),
    inference(avatar_split_clause,[],[f2176,f2170,f339,f171,f105,f98,f2194])).

fof(f2176,plain,
    ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41
    | ~ spl8_289 ),
    inference(unit_resulting_resolution,[],[f99,f106,f340,f172,f2171,f83])).

fof(f2186,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | spl8_41
    | spl8_287
    | spl8_289 ),
    inference(avatar_contradiction_clause,[],[f2185])).

fof(f2185,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41
    | ~ spl8_287
    | ~ spl8_289 ),
    inference(subsumption_resolution,[],[f2184,f340])).

fof(f2184,plain,
    ( r1_yellow_0(sK2,k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_287
    | ~ spl8_289 ),
    inference(subsumption_resolution,[],[f2178,f2165])).

fof(f2165,plain,
    ( ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_287 ),
    inference(avatar_component_clause,[],[f2164])).

fof(f2164,plain,
    ( spl8_287
  <=> ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_287])])).

fof(f2183,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | spl8_41
    | spl8_287
    | spl8_289 ),
    inference(avatar_contradiction_clause,[],[f2182])).

fof(f2182,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41
    | ~ spl8_287
    | ~ spl8_289 ),
    inference(subsumption_resolution,[],[f2173,f2165])).

fof(f2173,plain,
    ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41
    | ~ spl8_289 ),
    inference(unit_resulting_resolution,[],[f340,f2171,f1144])).

fof(f2172,plain,
    ( ~ spl8_287
    | ~ spl8_289
    | spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | spl8_41 ),
    inference(avatar_split_clause,[],[f1887,f339,f171,f105,f98,f2170,f2164])).

fof(f1887,plain,
    ( ~ r2_lattice3(sK2,k1_xboole_0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41 ),
    inference(forward_demodulation,[],[f1883,f115])).

fof(f1883,plain,
    ( ~ r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ r2_lattice3(sK2,k3_xboole_0(k1_xboole_0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41 ),
    inference(resolution,[],[f1319,f340])).

fof(f2159,plain,
    ( ~ spl8_285
    | spl8_275 ),
    inference(avatar_split_clause,[],[f2111,f2092,f2157])).

fof(f2157,plain,
    ( spl8_285
  <=> ~ r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)),sK6(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_285])])).

fof(f2111,plain,
    ( ~ r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)),sK6(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))))
    | ~ spl8_275 ),
    inference(unit_resulting_resolution,[],[f85,f2093,f123])).

fof(f2152,plain,
    ( spl8_282
    | spl8_267 ),
    inference(avatar_split_clause,[],[f2061,f2049,f2150])).

fof(f2150,plain,
    ( spl8_282
  <=> r2_hidden(sK6(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_282])])).

fof(f2049,plain,
    ( spl8_267
  <=> ~ v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_267])])).

fof(f2061,plain,
    ( r2_hidden(sK6(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)))
    | ~ spl8_267 ),
    inference(unit_resulting_resolution,[],[f85,f2050,f90])).

fof(f2050,plain,
    ( ~ v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)))
    | ~ spl8_267 ),
    inference(avatar_component_clause,[],[f2049])).

fof(f2145,plain,
    ( ~ spl8_281
    | spl8_267 ),
    inference(avatar_split_clause,[],[f2060,f2049,f2143])).

fof(f2143,plain,
    ( spl8_281
  <=> ~ r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)),sK6(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_281])])).

fof(f2060,plain,
    ( ~ r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)),sK6(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))))
    | ~ spl8_267 ),
    inference(unit_resulting_resolution,[],[f85,f2050,f123])).

fof(f2129,plain,
    ( spl8_278
    | spl8_271 ),
    inference(avatar_split_clause,[],[f2104,f2079,f2127])).

fof(f2127,plain,
    ( spl8_278
  <=> r2_hidden(sK6(sK6(sK6(sK6(sK6(k1_xboole_0))))),sK6(sK6(sK6(sK6(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_278])])).

fof(f2079,plain,
    ( spl8_271
  <=> ~ v1_xboole_0(sK6(sK6(sK6(sK6(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_271])])).

fof(f2104,plain,
    ( r2_hidden(sK6(sK6(sK6(sK6(sK6(k1_xboole_0))))),sK6(sK6(sK6(sK6(k1_xboole_0)))))
    | ~ spl8_271 ),
    inference(unit_resulting_resolution,[],[f85,f2080,f90])).

fof(f2080,plain,
    ( ~ v1_xboole_0(sK6(sK6(sK6(sK6(k1_xboole_0)))))
    | ~ spl8_271 ),
    inference(avatar_component_clause,[],[f2079])).

fof(f2122,plain,
    ( ~ spl8_277
    | spl8_271 ),
    inference(avatar_split_clause,[],[f2103,f2079,f2120])).

fof(f2120,plain,
    ( spl8_277
  <=> ~ r2_hidden(sK6(sK6(sK6(sK6(k1_xboole_0)))),sK6(sK6(sK6(sK6(sK6(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_277])])).

fof(f2103,plain,
    ( ~ r2_hidden(sK6(sK6(sK6(sK6(k1_xboole_0)))),sK6(sK6(sK6(sK6(sK6(k1_xboole_0))))))
    | ~ spl8_271 ),
    inference(unit_resulting_resolution,[],[f85,f2080,f123])).

fof(f2097,plain,
    ( ~ spl8_273
    | spl8_274
    | spl8_227 ),
    inference(avatar_split_clause,[],[f1798,f1688,f2095,f2089])).

fof(f1688,plain,
    ( spl8_227
  <=> ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_227])])).

fof(f1798,plain,
    ( v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))
    | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))
    | ~ spl8_227 ),
    inference(resolution,[],[f1689,f90])).

fof(f1689,plain,
    ( ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))
    | ~ spl8_227 ),
    inference(avatar_component_clause,[],[f1688])).

fof(f2084,plain,
    ( ~ spl8_269
    | spl8_270
    | spl8_173 ),
    inference(avatar_split_clause,[],[f1309,f1241,f2082,f2076])).

fof(f2076,plain,
    ( spl8_269
  <=> ~ m1_subset_1(sK6(sK6(sK6(k1_xboole_0))),sK6(sK6(sK6(sK6(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_269])])).

fof(f2082,plain,
    ( spl8_270
  <=> v1_xboole_0(sK6(sK6(sK6(sK6(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_270])])).

fof(f1241,plain,
    ( spl8_173
  <=> ~ r2_hidden(sK6(sK6(sK6(k1_xboole_0))),sK6(sK6(sK6(sK6(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_173])])).

fof(f1309,plain,
    ( v1_xboole_0(sK6(sK6(sK6(sK6(k1_xboole_0)))))
    | ~ m1_subset_1(sK6(sK6(sK6(k1_xboole_0))),sK6(sK6(sK6(sK6(k1_xboole_0)))))
    | ~ spl8_173 ),
    inference(resolution,[],[f1242,f90])).

fof(f1242,plain,
    ( ~ r2_hidden(sK6(sK6(sK6(k1_xboole_0))),sK6(sK6(sK6(sK6(k1_xboole_0)))))
    | ~ spl8_173 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f2054,plain,
    ( ~ spl8_265
    | spl8_266
    | spl8_213 ),
    inference(avatar_split_clause,[],[f1791,f1623,f2052,f2046])).

fof(f2046,plain,
    ( spl8_265
  <=> ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_265])])).

fof(f2052,plain,
    ( spl8_266
  <=> v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_266])])).

fof(f1623,plain,
    ( spl8_213
  <=> ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_213])])).

fof(f1791,plain,
    ( v1_xboole_0(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)))
    | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)))
    | ~ spl8_213 ),
    inference(resolution,[],[f1624,f90])).

fof(f1624,plain,
    ( ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)))
    | ~ spl8_213 ),
    inference(avatar_component_clause,[],[f1623])).

fof(f2028,plain,
    ( ~ spl8_263
    | spl8_231
    | spl8_261 ),
    inference(avatar_split_clause,[],[f2013,f2007,f1704,f2026])).

fof(f2026,plain,
    ( spl8_263
  <=> ~ m1_subset_1(k1_xboole_0,sK6(sK6(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_263])])).

fof(f1704,plain,
    ( spl8_231
  <=> ~ v1_xboole_0(sK6(sK6(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_231])])).

fof(f2007,plain,
    ( spl8_261
  <=> ~ r2_hidden(k1_xboole_0,sK6(sK6(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_261])])).

fof(f2013,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_231
    | ~ spl8_261 ),
    inference(unit_resulting_resolution,[],[f1705,f2008,f90])).

fof(f2008,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_261 ),
    inference(avatar_component_clause,[],[f2007])).

fof(f1705,plain,
    ( ~ v1_xboole_0(sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_231 ),
    inference(avatar_component_clause,[],[f1704])).

fof(f2012,plain,
    ( spl8_260
    | ~ spl8_236
    | ~ spl8_254 ),
    inference(avatar_split_clause,[],[f2001,f1960,f1781,f2010])).

fof(f2010,plain,
    ( spl8_260
  <=> r2_hidden(k1_xboole_0,sK6(sK6(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_260])])).

fof(f1781,plain,
    ( spl8_236
  <=> r2_hidden(sK6(sK6(sK6(u1_struct_0(sK2)))),sK6(sK6(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_236])])).

fof(f1960,plain,
    ( spl8_254
  <=> v1_xboole_0(sK6(sK6(sK6(u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_254])])).

fof(f2001,plain,
    ( r2_hidden(k1_xboole_0,sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_236
    | ~ spl8_254 ),
    inference(backward_demodulation,[],[f1993,f1782])).

fof(f1782,plain,
    ( r2_hidden(sK6(sK6(sK6(u1_struct_0(sK2)))),sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_236 ),
    inference(avatar_component_clause,[],[f1781])).

fof(f1993,plain,
    ( k1_xboole_0 = sK6(sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_254 ),
    inference(unit_resulting_resolution,[],[f1961,f74])).

fof(f1961,plain,
    ( v1_xboole_0(sK6(sK6(sK6(u1_struct_0(sK2)))))
    | ~ spl8_254 ),
    inference(avatar_component_clause,[],[f1960])).

fof(f1987,plain,
    ( spl8_258
    | spl8_255 ),
    inference(avatar_split_clause,[],[f1969,f1957,f1985])).

fof(f1985,plain,
    ( spl8_258
  <=> r2_hidden(sK6(sK6(sK6(sK6(u1_struct_0(sK2))))),sK6(sK6(sK6(u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_258])])).

fof(f1957,plain,
    ( spl8_255
  <=> ~ v1_xboole_0(sK6(sK6(sK6(u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_255])])).

fof(f1969,plain,
    ( r2_hidden(sK6(sK6(sK6(sK6(u1_struct_0(sK2))))),sK6(sK6(sK6(u1_struct_0(sK2)))))
    | ~ spl8_255 ),
    inference(unit_resulting_resolution,[],[f85,f1958,f90])).

fof(f1958,plain,
    ( ~ v1_xboole_0(sK6(sK6(sK6(u1_struct_0(sK2)))))
    | ~ spl8_255 ),
    inference(avatar_component_clause,[],[f1957])).

fof(f1979,plain,
    ( ~ spl8_257
    | spl8_255 ),
    inference(avatar_split_clause,[],[f1968,f1957,f1977])).

fof(f1977,plain,
    ( spl8_257
  <=> ~ r2_hidden(sK6(sK6(sK6(u1_struct_0(sK2)))),sK6(sK6(sK6(sK6(u1_struct_0(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_257])])).

fof(f1968,plain,
    ( ~ r2_hidden(sK6(sK6(sK6(u1_struct_0(sK2)))),sK6(sK6(sK6(sK6(u1_struct_0(sK2))))))
    | ~ spl8_255 ),
    inference(unit_resulting_resolution,[],[f85,f1958,f123])).

fof(f1962,plain,
    ( ~ spl8_253
    | spl8_254
    | spl8_233 ),
    inference(avatar_split_clause,[],[f1784,f1724,f1960,f1954])).

fof(f1954,plain,
    ( spl8_253
  <=> ~ m1_subset_1(sK6(sK6(u1_struct_0(sK2))),sK6(sK6(sK6(u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_253])])).

fof(f1724,plain,
    ( spl8_233
  <=> ~ r2_hidden(sK6(sK6(u1_struct_0(sK2))),sK6(sK6(sK6(u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_233])])).

fof(f1784,plain,
    ( v1_xboole_0(sK6(sK6(sK6(u1_struct_0(sK2)))))
    | ~ m1_subset_1(sK6(sK6(u1_struct_0(sK2))),sK6(sK6(sK6(u1_struct_0(sK2)))))
    | ~ spl8_233 ),
    inference(resolution,[],[f1725,f90])).

fof(f1725,plain,
    ( ~ r2_hidden(sK6(sK6(u1_struct_0(sK2))),sK6(sK6(sK6(u1_struct_0(sK2)))))
    | ~ spl8_233 ),
    inference(avatar_component_clause,[],[f1724])).

fof(f1908,plain,
    ( ~ spl8_251
    | spl8_205
    | spl8_249 ),
    inference(avatar_split_clause,[],[f1894,f1876,f1540,f1906])).

fof(f1906,plain,
    ( spl8_251
  <=> ~ m1_subset_1(k1_xboole_0,sK5(sK2,k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_251])])).

fof(f1540,plain,
    ( spl8_205
  <=> ~ v1_xboole_0(sK5(sK2,k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_205])])).

fof(f1876,plain,
    ( spl8_249
  <=> ~ r2_hidden(k1_xboole_0,sK5(sK2,k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_249])])).

fof(f1894,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_205
    | ~ spl8_249 ),
    inference(unit_resulting_resolution,[],[f1541,f1877,f90])).

fof(f1877,plain,
    ( ~ r2_hidden(k1_xboole_0,sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_249 ),
    inference(avatar_component_clause,[],[f1876])).

fof(f1541,plain,
    ( ~ v1_xboole_0(sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_205 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f1881,plain,
    ( spl8_248
    | ~ spl8_208
    | ~ spl8_242 ),
    inference(avatar_split_clause,[],[f1870,f1826,f1563,f1879])).

fof(f1879,plain,
    ( spl8_248
  <=> r2_hidden(k1_xboole_0,sK5(sK2,k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_248])])).

fof(f1563,plain,
    ( spl8_208
  <=> r2_hidden(sK6(sK5(sK2,k1_xboole_0,sK3)),sK5(sK2,k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_208])])).

fof(f1826,plain,
    ( spl8_242
  <=> v1_xboole_0(sK6(sK5(sK2,k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_242])])).

fof(f1870,plain,
    ( r2_hidden(k1_xboole_0,sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_208
    | ~ spl8_242 ),
    inference(backward_demodulation,[],[f1862,f1564])).

fof(f1564,plain,
    ( r2_hidden(sK6(sK5(sK2,k1_xboole_0,sK3)),sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_208 ),
    inference(avatar_component_clause,[],[f1563])).

fof(f1862,plain,
    ( k1_xboole_0 = sK6(sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_242 ),
    inference(unit_resulting_resolution,[],[f1827,f74])).

fof(f1827,plain,
    ( v1_xboole_0(sK6(sK5(sK2,k1_xboole_0,sK3)))
    | ~ spl8_242 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f1856,plain,
    ( spl8_246
    | spl8_243 ),
    inference(avatar_split_clause,[],[f1835,f1823,f1854])).

fof(f1854,plain,
    ( spl8_246
  <=> r2_hidden(sK6(sK6(sK5(sK2,k1_xboole_0,sK3))),sK6(sK5(sK2,k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_246])])).

fof(f1823,plain,
    ( spl8_243
  <=> ~ v1_xboole_0(sK6(sK5(sK2,k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_243])])).

fof(f1835,plain,
    ( r2_hidden(sK6(sK6(sK5(sK2,k1_xboole_0,sK3))),sK6(sK5(sK2,k1_xboole_0,sK3)))
    | ~ spl8_243 ),
    inference(unit_resulting_resolution,[],[f85,f1824,f90])).

fof(f1824,plain,
    ( ~ v1_xboole_0(sK6(sK5(sK2,k1_xboole_0,sK3)))
    | ~ spl8_243 ),
    inference(avatar_component_clause,[],[f1823])).

fof(f1849,plain,
    ( ~ spl8_245
    | spl8_243 ),
    inference(avatar_split_clause,[],[f1834,f1823,f1847])).

fof(f1847,plain,
    ( spl8_245
  <=> ~ r2_hidden(sK6(sK5(sK2,k1_xboole_0,sK3)),sK6(sK6(sK5(sK2,k1_xboole_0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_245])])).

fof(f1834,plain,
    ( ~ r2_hidden(sK6(sK5(sK2,k1_xboole_0,sK3)),sK6(sK6(sK5(sK2,k1_xboole_0,sK3))))
    | ~ spl8_243 ),
    inference(unit_resulting_resolution,[],[f85,f1824,f123])).

fof(f1828,plain,
    ( ~ spl8_241
    | spl8_242
    | spl8_207 ),
    inference(avatar_split_clause,[],[f1612,f1556,f1826,f1820])).

fof(f1820,plain,
    ( spl8_241
  <=> ~ m1_subset_1(sK5(sK2,k1_xboole_0,sK3),sK6(sK5(sK2,k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_241])])).

fof(f1556,plain,
    ( spl8_207
  <=> ~ r2_hidden(sK5(sK2,k1_xboole_0,sK3),sK6(sK5(sK2,k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_207])])).

fof(f1612,plain,
    ( v1_xboole_0(sK6(sK5(sK2,k1_xboole_0,sK3)))
    | ~ m1_subset_1(sK5(sK2,k1_xboole_0,sK3),sK6(sK5(sK2,k1_xboole_0,sK3)))
    | ~ spl8_207 ),
    inference(resolution,[],[f1557,f90])).

fof(f1557,plain,
    ( ~ r2_hidden(sK5(sK2,k1_xboole_0,sK3),sK6(sK5(sK2,k1_xboole_0,sK3)))
    | ~ spl8_207 ),
    inference(avatar_component_clause,[],[f1556])).

fof(f1815,plain,
    ( ~ spl8_239
    | spl8_1
    | ~ spl8_2
    | ~ spl8_82
    | spl8_159 ),
    inference(avatar_split_clause,[],[f1166,f1160,f631,f105,f98,f1813])).

fof(f1813,plain,
    ( spl8_239
  <=> ~ r1_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))),sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_239])])).

fof(f631,plain,
    ( spl8_82
  <=> m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f1160,plain,
    ( spl8_159
  <=> ~ r1_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_159])])).

fof(f1166,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_82
    | ~ spl8_159 ),
    inference(forward_demodulation,[],[f1164,f87])).

fof(f1164,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_82
    | ~ spl8_159 ),
    inference(unit_resulting_resolution,[],[f99,f106,f632,f1161,f78])).

fof(f1161,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_159 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f632,plain,
    ( m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f631])).

fof(f1783,plain,
    ( spl8_236
    | spl8_231 ),
    inference(avatar_split_clause,[],[f1716,f1704,f1781])).

fof(f1716,plain,
    ( r2_hidden(sK6(sK6(sK6(u1_struct_0(sK2)))),sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_231 ),
    inference(unit_resulting_resolution,[],[f85,f1705,f90])).

fof(f1753,plain,
    ( spl8_113
    | ~ spl8_146
    | ~ spl8_170 ),
    inference(avatar_contradiction_clause,[],[f1752])).

fof(f1752,plain,
    ( $false
    | ~ spl8_113
    | ~ spl8_146
    | ~ spl8_170 ),
    inference(subsumption_resolution,[],[f1745,f830])).

fof(f1745,plain,
    ( r2_hidden(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_146
    | ~ spl8_170 ),
    inference(backward_demodulation,[],[f1739,f1064])).

fof(f1064,plain,
    ( r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_146 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1063,plain,
    ( spl8_146
  <=> r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).

fof(f1739,plain,
    ( k1_xboole_0 = sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)
    | ~ spl8_170 ),
    inference(unit_resulting_resolution,[],[f1226,f74])).

fof(f1226,plain,
    ( v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_170 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f1225,plain,
    ( spl8_170
  <=> v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_170])])).

fof(f1751,plain,
    ( spl8_117
    | ~ spl8_140
    | ~ spl8_170 ),
    inference(avatar_contradiction_clause,[],[f1750])).

fof(f1750,plain,
    ( $false
    | ~ spl8_117
    | ~ spl8_140
    | ~ spl8_170 ),
    inference(subsumption_resolution,[],[f1743,f850])).

fof(f1743,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_140
    | ~ spl8_170 ),
    inference(backward_demodulation,[],[f1739,f1027])).

fof(f1733,plain,
    ( spl8_234
    | spl8_171 ),
    inference(avatar_split_clause,[],[f1233,f1222,f1731])).

fof(f1222,plain,
    ( spl8_171
  <=> ~ v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_171])])).

fof(f1233,plain,
    ( r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_171 ),
    inference(unit_resulting_resolution,[],[f85,f1223,f90])).

fof(f1223,plain,
    ( ~ v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_171 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f1726,plain,
    ( ~ spl8_233
    | spl8_231 ),
    inference(avatar_split_clause,[],[f1715,f1704,f1724])).

fof(f1715,plain,
    ( ~ r2_hidden(sK6(sK6(u1_struct_0(sK2))),sK6(sK6(sK6(u1_struct_0(sK2)))))
    | ~ spl8_231 ),
    inference(unit_resulting_resolution,[],[f85,f1705,f123])).

fof(f1709,plain,
    ( ~ spl8_229
    | spl8_230
    | spl8_109 ),
    inference(avatar_split_clause,[],[f1420,f798,f1707,f1701])).

fof(f1701,plain,
    ( spl8_229
  <=> ~ m1_subset_1(sK6(u1_struct_0(sK2)),sK6(sK6(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_229])])).

fof(f1707,plain,
    ( spl8_230
  <=> v1_xboole_0(sK6(sK6(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_230])])).

fof(f798,plain,
    ( spl8_109
  <=> ~ r2_hidden(sK6(u1_struct_0(sK2)),sK6(sK6(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f1420,plain,
    ( v1_xboole_0(sK6(sK6(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK6(u1_struct_0(sK2)),sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_109 ),
    inference(resolution,[],[f799,f90])).

fof(f799,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK2)),sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_109 ),
    inference(avatar_component_clause,[],[f798])).

fof(f1690,plain,
    ( ~ spl8_227
    | spl8_171 ),
    inference(avatar_split_clause,[],[f1232,f1222,f1688])).

fof(f1232,plain,
    ( ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)))
    | ~ spl8_171 ),
    inference(unit_resulting_resolution,[],[f85,f1223,f123])).

fof(f1675,plain,
    ( spl8_224
    | spl8_33
    | ~ spl8_214 ),
    inference(avatar_split_clause,[],[f1638,f1630,f263,f1673])).

fof(f1630,plain,
    ( spl8_214
  <=> m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_214])])).

fof(f1638,plain,
    ( r2_hidden(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_214 ),
    inference(unit_resulting_resolution,[],[f264,f1631,f90])).

fof(f1631,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2))
    | ~ spl8_214 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f1668,plain,
    ( ~ spl8_223
    | spl8_33
    | ~ spl8_214 ),
    inference(avatar_split_clause,[],[f1637,f1630,f263,f1666])).

fof(f1666,plain,
    ( spl8_223
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_223])])).

fof(f1637,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3))
    | ~ spl8_33
    | ~ spl8_214 ),
    inference(unit_resulting_resolution,[],[f264,f1631,f123])).

fof(f1661,plain,
    ( spl8_220
    | spl8_163 ),
    inference(avatar_split_clause,[],[f1188,f1177,f1659])).

fof(f1659,plain,
    ( spl8_220
  <=> r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_220])])).

fof(f1177,plain,
    ( spl8_163
  <=> ~ v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_163])])).

fof(f1188,plain,
    ( r2_hidden(sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_163 ),
    inference(unit_resulting_resolution,[],[f85,f1178,f90])).

fof(f1178,plain,
    ( ~ v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_163 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f1654,plain,
    ( spl8_218
    | spl8_33
    | ~ spl8_194 ),
    inference(avatar_split_clause,[],[f1634,f1478,f263,f1652])).

fof(f1652,plain,
    ( spl8_218
  <=> r2_hidden(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_218])])).

fof(f1478,plain,
    ( spl8_194
  <=> m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_194])])).

fof(f1634,plain,
    ( r2_hidden(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_194 ),
    inference(unit_resulting_resolution,[],[f264,f1479,f90])).

fof(f1479,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_194 ),
    inference(avatar_component_clause,[],[f1478])).

fof(f1647,plain,
    ( ~ spl8_217
    | spl8_33
    | ~ spl8_194 ),
    inference(avatar_split_clause,[],[f1633,f1478,f263,f1645])).

fof(f1645,plain,
    ( spl8_217
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_217])])).

fof(f1633,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),k1_xboole_0))
    | ~ spl8_33
    | ~ spl8_194 ),
    inference(unit_resulting_resolution,[],[f264,f1479,f123])).

fof(f1632,plain,
    ( spl8_214
    | spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_190 ),
    inference(avatar_split_clause,[],[f1455,f1451,f163,f105,f98,f1630])).

fof(f1451,plain,
    ( spl8_190
  <=> r1_yellow_0(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_190])])).

fof(f1455,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK3),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_190 ),
    inference(unit_resulting_resolution,[],[f99,f106,f164,f1452,f82])).

fof(f1452,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_190 ),
    inference(avatar_component_clause,[],[f1451])).

fof(f1625,plain,
    ( ~ spl8_213
    | spl8_163 ),
    inference(avatar_split_clause,[],[f1187,f1177,f1623])).

fof(f1187,plain,
    ( ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),sK6(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)))
    | ~ spl8_163 ),
    inference(unit_resulting_resolution,[],[f85,f1178,f123])).

fof(f1594,plain,
    ( spl8_210
    | ~ spl8_204 ),
    inference(avatar_split_clause,[],[f1572,f1543,f1592])).

fof(f1592,plain,
    ( spl8_210
  <=> k1_xboole_0 = sK5(sK2,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_210])])).

fof(f1543,plain,
    ( spl8_204
  <=> v1_xboole_0(sK5(sK2,k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_204])])).

fof(f1572,plain,
    ( k1_xboole_0 = sK5(sK2,k1_xboole_0,sK3)
    | ~ spl8_204 ),
    inference(unit_resulting_resolution,[],[f1544,f74])).

fof(f1544,plain,
    ( v1_xboole_0(sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_204 ),
    inference(avatar_component_clause,[],[f1543])).

fof(f1565,plain,
    ( spl8_208
    | spl8_205 ),
    inference(avatar_split_clause,[],[f1548,f1540,f1563])).

fof(f1548,plain,
    ( r2_hidden(sK6(sK5(sK2,k1_xboole_0,sK3)),sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_205 ),
    inference(unit_resulting_resolution,[],[f85,f1541,f90])).

fof(f1558,plain,
    ( ~ spl8_207
    | spl8_205 ),
    inference(avatar_split_clause,[],[f1547,f1540,f1556])).

fof(f1547,plain,
    ( ~ r2_hidden(sK5(sK2,k1_xboole_0,sK3),sK6(sK5(sK2,k1_xboole_0,sK3)))
    | ~ spl8_205 ),
    inference(unit_resulting_resolution,[],[f85,f1541,f123])).

fof(f1545,plain,
    ( ~ spl8_203
    | spl8_204
    | spl8_199 ),
    inference(avatar_split_clause,[],[f1529,f1507,f1543,f1537])).

fof(f1537,plain,
    ( spl8_203
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_203])])).

fof(f1507,plain,
    ( spl8_199
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_199])])).

fof(f1529,plain,
    ( v1_xboole_0(sK5(sK2,k1_xboole_0,sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_199 ),
    inference(resolution,[],[f1508,f90])).

fof(f1508,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_199 ),
    inference(avatar_component_clause,[],[f1507])).

fof(f1519,plain,
    ( spl8_200
    | spl8_33
    | ~ spl8_196 ),
    inference(avatar_split_clause,[],[f1500,f1496,f263,f1517])).

fof(f1517,plain,
    ( spl8_200
  <=> r2_hidden(sK5(sK2,k1_xboole_0,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_200])])).

fof(f1496,plain,
    ( spl8_196
  <=> m1_subset_1(sK5(sK2,k1_xboole_0,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_196])])).

fof(f1500,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0,sK3),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_196 ),
    inference(unit_resulting_resolution,[],[f264,f1497,f90])).

fof(f1497,plain,
    ( m1_subset_1(sK5(sK2,k1_xboole_0,sK3),u1_struct_0(sK2))
    | ~ spl8_196 ),
    inference(avatar_component_clause,[],[f1496])).

fof(f1509,plain,
    ( ~ spl8_199
    | spl8_33
    | ~ spl8_196 ),
    inference(avatar_split_clause,[],[f1499,f1496,f263,f1507])).

fof(f1499,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k1_xboole_0,sK3))
    | ~ spl8_33
    | ~ spl8_196 ),
    inference(unit_resulting_resolution,[],[f264,f1497,f123])).

fof(f1498,plain,
    ( spl8_196
    | spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f1481,f342,f163,f105,f98,f1496])).

fof(f342,plain,
    ( spl8_40
  <=> r1_yellow_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f1481,plain,
    ( m1_subset_1(sK5(sK2,k1_xboole_0,sK3),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f99,f106,f164,f343,f82])).

fof(f343,plain,
    ( r1_yellow_0(sK2,k1_xboole_0)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f342])).

fof(f1480,plain,
    ( spl8_194
    | spl8_1
    | ~ spl8_2
    | spl8_41
    | ~ spl8_190 ),
    inference(avatar_split_clause,[],[f1454,f1451,f339,f105,f98,f1478])).

fof(f1454,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_41
    | ~ spl8_190 ),
    inference(unit_resulting_resolution,[],[f99,f106,f340,f1452,f82])).

fof(f1472,plain,
    ( ~ spl8_193
    | ~ spl8_190 ),
    inference(avatar_split_clause,[],[f1456,f1451,f1470])).

fof(f1470,plain,
    ( spl8_193
  <=> ~ sP1(k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_193])])).

fof(f1456,plain,
    ( ~ sP1(k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK2)
    | ~ spl8_190 ),
    inference(unit_resulting_resolution,[],[f1452,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ r1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X1,X0)
        & r1_yellow_0(X1,k3_xboole_0(X0,u1_struct_0(X1))) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ( ~ r1_yellow_0(X0,X1)
        & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ( ~ r1_yellow_0(X0,X1)
        & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1453,plain,
    ( spl8_190
    | spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f1443,f171,f105,f98,f1451])).

fof(f1443,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f1437,f1108])).

fof(f1437,plain,
    ( r2_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2)))))
    | r1_yellow_0(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16 ),
    inference(factoring,[],[f1144])).

fof(f1433,plain,
    ( spl8_188
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f1342,f887,f1431])).

fof(f1431,plain,
    ( spl8_188
  <=> k1_xboole_0 = sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_188])])).

fof(f887,plain,
    ( spl8_124
  <=> v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f1342,plain,
    ( k1_xboole_0 = sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_124 ),
    inference(unit_resulting_resolution,[],[f888,f74])).

fof(f888,plain,
    ( v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_124 ),
    inference(avatar_component_clause,[],[f887])).

fof(f1394,plain,
    ( ~ spl8_187
    | ~ spl8_124
    | spl8_137 ),
    inference(avatar_split_clause,[],[f1352,f950,f887,f1392])).

fof(f1392,plain,
    ( spl8_187
  <=> ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_187])])).

fof(f950,plain,
    ( spl8_137
  <=> ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f1352,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)
    | ~ spl8_124
    | ~ spl8_137 ),
    inference(backward_demodulation,[],[f1342,f951])).

fof(f951,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_137 ),
    inference(avatar_component_clause,[],[f950])).

fof(f1387,plain,
    ( ~ spl8_113
    | spl8_103
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f1348,f887,f751,f829])).

fof(f751,plain,
    ( spl8_103
  <=> ~ r2_hidden(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f1348,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_103
    | ~ spl8_124 ),
    inference(backward_demodulation,[],[f1342,f752])).

fof(f752,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_103 ),
    inference(avatar_component_clause,[],[f751])).

fof(f1385,plain,
    ( ~ spl8_185
    | ~ spl8_124
    | spl8_139 ),
    inference(avatar_split_clause,[],[f1353,f956,f887,f1383])).

fof(f1383,plain,
    ( spl8_185
  <=> ~ r1_lattice3(sK2,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_185])])).

fof(f956,plain,
    ( spl8_139
  <=> ~ r1_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_139])])).

fof(f1353,plain,
    ( ~ r1_lattice3(sK2,sK3,k1_xboole_0)
    | ~ spl8_124
    | ~ spl8_139 ),
    inference(backward_demodulation,[],[f1342,f957])).

fof(f957,plain,
    ( ~ r1_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_139 ),
    inference(avatar_component_clause,[],[f956])).

fof(f1367,plain,
    ( ~ spl8_117
    | spl8_27
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f1346,f887,f227,f849])).

fof(f227,plain,
    ( spl8_27
  <=> ~ m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f1346,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_27
    | ~ spl8_124 ),
    inference(backward_demodulation,[],[f1342,f228])).

fof(f228,plain,
    ( ~ m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f227])).

fof(f1366,plain,
    ( spl8_36
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f1351,f887,f319])).

fof(f319,plain,
    ( spl8_36
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f1351,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_124 ),
    inference(backward_demodulation,[],[f1342,f888])).

fof(f1365,plain,
    ( spl8_37
    | ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f1364])).

fof(f1364,plain,
    ( $false
    | ~ spl8_37
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f317,f1351])).

fof(f317,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl8_37
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f1360,plain,
    ( spl8_103
    | ~ spl8_112
    | ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f1359])).

fof(f1359,plain,
    ( $false
    | ~ spl8_103
    | ~ spl8_112
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1348,f833])).

fof(f833,plain,
    ( r2_hidden(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_112 ),
    inference(avatar_component_clause,[],[f832])).

fof(f832,plain,
    ( spl8_112
  <=> r2_hidden(k1_xboole_0,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).

fof(f1358,plain,
    ( spl8_27
    | ~ spl8_116
    | ~ spl8_124 ),
    inference(avatar_contradiction_clause,[],[f1357])).

fof(f1357,plain,
    ( $false
    | ~ spl8_27
    | ~ spl8_116
    | ~ spl8_124 ),
    inference(subsumption_resolution,[],[f1346,f853])).

fof(f853,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_116 ),
    inference(avatar_component_clause,[],[f852])).

fof(f852,plain,
    ( spl8_116
  <=> m1_subset_1(k1_xboole_0,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f1336,plain,
    ( spl8_182
    | spl8_125 ),
    inference(avatar_split_clause,[],[f924,f884,f1334])).

fof(f1334,plain,
    ( spl8_182
  <=> r2_hidden(sK6(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_182])])).

fof(f884,plain,
    ( spl8_125
  <=> ~ v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_125])])).

fof(f924,plain,
    ( r2_hidden(sK6(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_125 ),
    inference(unit_resulting_resolution,[],[f85,f885,f90])).

fof(f885,plain,
    ( ~ v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_125 ),
    inference(avatar_component_clause,[],[f884])).

fof(f1329,plain,
    ( ~ spl8_181
    | spl8_125 ),
    inference(avatar_split_clause,[],[f923,f884,f1327])).

fof(f1327,plain,
    ( spl8_181
  <=> ~ r2_hidden(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),sK6(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_181])])).

fof(f923,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),sK6(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))))
    | ~ spl8_125 ),
    inference(unit_resulting_resolution,[],[f85,f885,f123])).

fof(f1294,plain,
    ( ~ spl8_179
    | spl8_151
    | spl8_177 ),
    inference(avatar_split_clause,[],[f1280,f1274,f1090,f1292])).

fof(f1292,plain,
    ( spl8_179
  <=> ~ m1_subset_1(k1_xboole_0,sK6(sK6(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_179])])).

fof(f1090,plain,
    ( spl8_151
  <=> ~ v1_xboole_0(sK6(sK6(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f1274,plain,
    ( spl8_177
  <=> ~ r2_hidden(k1_xboole_0,sK6(sK6(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_177])])).

fof(f1280,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK6(sK6(k1_xboole_0)))
    | ~ spl8_151
    | ~ spl8_177 ),
    inference(unit_resulting_resolution,[],[f1091,f1275,f90])).

fof(f1275,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(sK6(k1_xboole_0)))
    | ~ spl8_177 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1091,plain,
    ( ~ v1_xboole_0(sK6(sK6(k1_xboole_0)))
    | ~ spl8_151 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1279,plain,
    ( spl8_176
    | ~ spl8_154
    | ~ spl8_166 ),
    inference(avatar_split_clause,[],[f1264,f1202,f1120,f1277])).

fof(f1277,plain,
    ( spl8_176
  <=> r2_hidden(k1_xboole_0,sK6(sK6(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_176])])).

fof(f1120,plain,
    ( spl8_154
  <=> r2_hidden(sK6(sK6(sK6(k1_xboole_0))),sK6(sK6(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f1202,plain,
    ( spl8_166
  <=> v1_xboole_0(sK6(sK6(sK6(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_166])])).

fof(f1264,plain,
    ( r2_hidden(k1_xboole_0,sK6(sK6(k1_xboole_0)))
    | ~ spl8_154
    | ~ spl8_166 ),
    inference(backward_demodulation,[],[f1256,f1121])).

fof(f1121,plain,
    ( r2_hidden(sK6(sK6(sK6(k1_xboole_0))),sK6(sK6(k1_xboole_0)))
    | ~ spl8_154 ),
    inference(avatar_component_clause,[],[f1120])).

fof(f1256,plain,
    ( k1_xboole_0 = sK6(sK6(sK6(k1_xboole_0)))
    | ~ spl8_166 ),
    inference(unit_resulting_resolution,[],[f1203,f74])).

fof(f1203,plain,
    ( v1_xboole_0(sK6(sK6(sK6(k1_xboole_0))))
    | ~ spl8_166 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1250,plain,
    ( spl8_174
    | spl8_167 ),
    inference(avatar_split_clause,[],[f1211,f1199,f1248])).

fof(f1248,plain,
    ( spl8_174
  <=> r2_hidden(sK6(sK6(sK6(sK6(k1_xboole_0)))),sK6(sK6(sK6(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_174])])).

fof(f1199,plain,
    ( spl8_167
  <=> ~ v1_xboole_0(sK6(sK6(sK6(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_167])])).

fof(f1211,plain,
    ( r2_hidden(sK6(sK6(sK6(sK6(k1_xboole_0)))),sK6(sK6(sK6(k1_xboole_0))))
    | ~ spl8_167 ),
    inference(unit_resulting_resolution,[],[f85,f1200,f90])).

fof(f1200,plain,
    ( ~ v1_xboole_0(sK6(sK6(sK6(k1_xboole_0))))
    | ~ spl8_167 ),
    inference(avatar_component_clause,[],[f1199])).

fof(f1243,plain,
    ( ~ spl8_173
    | spl8_167 ),
    inference(avatar_split_clause,[],[f1210,f1199,f1241])).

fof(f1210,plain,
    ( ~ r2_hidden(sK6(sK6(sK6(k1_xboole_0))),sK6(sK6(sK6(sK6(k1_xboole_0)))))
    | ~ spl8_167 ),
    inference(unit_resulting_resolution,[],[f85,f1200,f123])).

fof(f1227,plain,
    ( ~ spl8_169
    | spl8_170
    | spl8_33
    | ~ spl8_140 ),
    inference(avatar_split_clause,[],[f1032,f1026,f263,f1225,f1219])).

fof(f1219,plain,
    ( spl8_169
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_169])])).

fof(f1032,plain,
    ( v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_33
    | ~ spl8_140 ),
    inference(subsumption_resolution,[],[f1031,f264])).

fof(f1031,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_140 ),
    inference(resolution,[],[f1027,f124])).

fof(f1204,plain,
    ( ~ spl8_165
    | spl8_166
    | spl8_153 ),
    inference(avatar_split_clause,[],[f1123,f1113,f1202,f1196])).

fof(f1196,plain,
    ( spl8_165
  <=> ~ m1_subset_1(sK6(sK6(k1_xboole_0)),sK6(sK6(sK6(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).

fof(f1113,plain,
    ( spl8_153
  <=> ~ r2_hidden(sK6(sK6(k1_xboole_0)),sK6(sK6(sK6(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_153])])).

fof(f1123,plain,
    ( v1_xboole_0(sK6(sK6(sK6(k1_xboole_0))))
    | ~ m1_subset_1(sK6(sK6(k1_xboole_0)),sK6(sK6(sK6(k1_xboole_0))))
    | ~ spl8_153 ),
    inference(resolution,[],[f1114,f90])).

fof(f1114,plain,
    ( ~ r2_hidden(sK6(sK6(k1_xboole_0)),sK6(sK6(sK6(k1_xboole_0))))
    | ~ spl8_153 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f1182,plain,
    ( ~ spl8_161
    | spl8_162
    | ~ spl8_24
    | spl8_33 ),
    inference(avatar_split_clause,[],[f1021,f263,f218,f1180,f1174])).

fof(f1174,plain,
    ( spl8_161
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).

fof(f1180,plain,
    ( spl8_162
  <=> v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_162])])).

fof(f1021,plain,
    ( v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_24
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f1020,f264])).

fof(f1020,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_24 ),
    inference(resolution,[],[f219,f124])).

fof(f1162,plain,
    ( ~ spl8_159
    | spl8_1
    | ~ spl8_2
    | ~ spl8_82
    | spl8_135 ),
    inference(avatar_split_clause,[],[f1079,f946,f631,f105,f98,f1160])).

fof(f946,plain,
    ( spl8_135
  <=> ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_135])])).

fof(f1079,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(u1_struct_0(sK2),k3_xboole_0(sK3,u1_struct_0(sK2))),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_82
    | ~ spl8_135 ),
    inference(forward_demodulation,[],[f1077,f87])).

fof(f1077,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(k3_xboole_0(sK3,u1_struct_0(sK2)),u1_struct_0(sK2)),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_82
    | ~ spl8_135 ),
    inference(unit_resulting_resolution,[],[f99,f106,f632,f947,f78])).

fof(f947,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_135 ),
    inference(avatar_component_clause,[],[f946])).

fof(f1136,plain,
    ( spl8_156
    | spl8_75 ),
    inference(avatar_split_clause,[],[f557,f545,f1134])).

fof(f1134,plain,
    ( spl8_156
  <=> r2_hidden(sK6(sK6(sK4(sK2,sK3,k1_xboole_0))),sK6(sK4(sK2,sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).

fof(f545,plain,
    ( spl8_75
  <=> ~ v1_xboole_0(sK6(sK4(sK2,sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f557,plain,
    ( r2_hidden(sK6(sK6(sK4(sK2,sK3,k1_xboole_0))),sK6(sK4(sK2,sK3,k1_xboole_0)))
    | ~ spl8_75 ),
    inference(unit_resulting_resolution,[],[f85,f546,f90])).

fof(f546,plain,
    ( ~ v1_xboole_0(sK6(sK4(sK2,sK3,k1_xboole_0)))
    | ~ spl8_75 ),
    inference(avatar_component_clause,[],[f545])).

fof(f1122,plain,
    ( spl8_154
    | spl8_151 ),
    inference(avatar_split_clause,[],[f1102,f1090,f1120])).

fof(f1102,plain,
    ( r2_hidden(sK6(sK6(sK6(k1_xboole_0))),sK6(sK6(k1_xboole_0)))
    | ~ spl8_151 ),
    inference(unit_resulting_resolution,[],[f85,f1091,f90])).

fof(f1115,plain,
    ( ~ spl8_153
    | spl8_151 ),
    inference(avatar_split_clause,[],[f1101,f1090,f1113])).

fof(f1101,plain,
    ( ~ r2_hidden(sK6(sK6(k1_xboole_0)),sK6(sK6(sK6(k1_xboole_0))))
    | ~ spl8_151 ),
    inference(unit_resulting_resolution,[],[f85,f1091,f123])).

fof(f1095,plain,
    ( ~ spl8_149
    | spl8_150
    | spl8_131 ),
    inference(avatar_split_clause,[],[f933,f916,f1093,f1087])).

fof(f1087,plain,
    ( spl8_149
  <=> ~ m1_subset_1(sK6(k1_xboole_0),sK6(sK6(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f1093,plain,
    ( spl8_150
  <=> v1_xboole_0(sK6(sK6(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f916,plain,
    ( spl8_131
  <=> ~ r2_hidden(sK6(k1_xboole_0),sK6(sK6(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).

fof(f933,plain,
    ( v1_xboole_0(sK6(sK6(k1_xboole_0)))
    | ~ m1_subset_1(sK6(k1_xboole_0),sK6(sK6(k1_xboole_0)))
    | ~ spl8_131 ),
    inference(resolution,[],[f917,f90])).

fof(f917,plain,
    ( ~ r2_hidden(sK6(k1_xboole_0),sK6(sK6(k1_xboole_0)))
    | ~ spl8_131 ),
    inference(avatar_component_clause,[],[f916])).

fof(f1065,plain,
    ( spl8_146
    | spl8_33
    | ~ spl8_140 ),
    inference(avatar_split_clause,[],[f1030,f1026,f263,f1063])).

fof(f1030,plain,
    ( r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_140 ),
    inference(unit_resulting_resolution,[],[f264,f1027,f90])).

fof(f1058,plain,
    ( ~ spl8_145
    | spl8_33
    | ~ spl8_140 ),
    inference(avatar_split_clause,[],[f1029,f1026,f263,f1056])).

fof(f1056,plain,
    ( spl8_145
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).

fof(f1029,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0))
    | ~ spl8_33
    | ~ spl8_140 ),
    inference(unit_resulting_resolution,[],[f264,f1027,f123])).

fof(f1051,plain,
    ( ~ spl8_143
    | ~ spl8_24
    | spl8_33 ),
    inference(avatar_split_clause,[],[f1018,f263,f218,f1049])).

fof(f1049,plain,
    ( spl8_143
  <=> ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).

fof(f1018,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ spl8_24
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f264,f219,f123])).

fof(f1028,plain,
    ( spl8_140
    | spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | spl8_41 ),
    inference(avatar_split_clause,[],[f1002,f339,f171,f105,f98,f1026])).

fof(f1002,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_16
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f99,f106,f340,f172,f82])).

fof(f994,plain,
    ( ~ spl8_24
    | spl8_31
    | spl8_33 ),
    inference(avatar_contradiction_clause,[],[f993])).

fof(f993,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_31
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f219,f992])).

fof(f992,plain,
    ( ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_31
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f742,f264])).

fof(f742,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_31 ),
    inference(resolution,[],[f251,f90])).

fof(f251,plain,
    ( ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl8_31
  <=> ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f991,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_136
    | spl8_139 ),
    inference(avatar_contradiction_clause,[],[f990])).

fof(f990,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_136
    | ~ spl8_139 ),
    inference(subsumption_resolution,[],[f989,f954])).

fof(f954,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_136 ),
    inference(avatar_component_clause,[],[f953])).

fof(f953,plain,
    ( spl8_136
  <=> r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_136])])).

fof(f989,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_139 ),
    inference(subsumption_resolution,[],[f984,f231])).

fof(f231,plain,
    ( m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl8_26
  <=> m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f984,plain,
    ( ~ m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_139 ),
    inference(resolution,[],[f957,f374])).

fof(f988,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_136
    | spl8_139 ),
    inference(avatar_contradiction_clause,[],[f987])).

fof(f987,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_136
    | ~ spl8_139 ),
    inference(subsumption_resolution,[],[f981,f954])).

fof(f981,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_139 ),
    inference(unit_resulting_resolution,[],[f231,f957,f374])).

fof(f986,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_136
    | spl8_139 ),
    inference(avatar_contradiction_clause,[],[f985])).

fof(f985,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_136
    | ~ spl8_139 ),
    inference(subsumption_resolution,[],[f983,f954])).

fof(f983,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_139 ),
    inference(unit_resulting_resolution,[],[f99,f106,f231,f957,f78])).

fof(f978,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | spl8_13
    | ~ spl8_26
    | ~ spl8_138 ),
    inference(avatar_contradiction_clause,[],[f977])).

fof(f977,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_26
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f963,f976])).

fof(f976,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f975,f99])).

fof(f975,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f974,f106])).

fof(f974,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_26
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f965,f231])).

fof(f965,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_138 ),
    inference(resolution,[],[f960,f77])).

fof(f960,plain,
    ( r1_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_138 ),
    inference(avatar_component_clause,[],[f959])).

fof(f959,plain,
    ( spl8_138
  <=> r1_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f963,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f99,f106,f147,f150,f960,f81])).

fof(f150,plain,
    ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_13
  <=> ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f147,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl8_10
  <=> r2_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f973,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | spl8_137
    | ~ spl8_138 ),
    inference(avatar_contradiction_clause,[],[f972])).

fof(f972,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_137
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f971,f99])).

fof(f971,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_137
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f970,f106])).

fof(f970,plain,
    ( ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_26
    | ~ spl8_137
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f969,f231])).

fof(f969,plain,
    ( ~ m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_137
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f965,f951])).

fof(f967,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | spl8_137
    | ~ spl8_138 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_137
    | ~ spl8_138 ),
    inference(subsumption_resolution,[],[f964,f951])).

fof(f964,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_26
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f99,f106,f231,f960,f77])).

fof(f961,plain,
    ( spl8_136
    | spl8_138
    | spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | spl8_13 ),
    inference(avatar_split_clause,[],[f808,f149,f146,f105,f98,f959,f953])).

fof(f808,plain,
    ( r1_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_13 ),
    inference(resolution,[],[f617,f147])).

fof(f617,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK2,X0)
        | r1_lattice3(sK2,X0,sK4(sK2,X0,k3_xboole_0(sK3,u1_struct_0(sK2))))
        | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,X0,k3_xboole_0(sK3,u1_struct_0(sK2)))) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(resolution,[],[f150,f400])).

fof(f948,plain,
    ( ~ spl8_135
    | spl8_1
    | ~ spl8_2
    | spl8_79
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f679,f631,f587,f105,f98,f946])).

fof(f587,plain,
    ( spl8_79
  <=> ~ r1_lattice3(sK2,sK3,sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f679,plain,
    ( ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_79
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f99,f106,f632,f588,f78])).

fof(f588,plain,
    ( ~ r1_lattice3(sK2,sK3,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_79 ),
    inference(avatar_component_clause,[],[f587])).

fof(f932,plain,
    ( spl8_132
    | spl8_129 ),
    inference(avatar_split_clause,[],[f908,f900,f930])).

fof(f930,plain,
    ( spl8_132
  <=> r2_hidden(sK6(sK6(k1_xboole_0)),sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).

fof(f900,plain,
    ( spl8_129
  <=> ~ v1_xboole_0(sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).

fof(f908,plain,
    ( r2_hidden(sK6(sK6(k1_xboole_0)),sK6(k1_xboole_0))
    | ~ spl8_129 ),
    inference(unit_resulting_resolution,[],[f85,f901,f90])).

fof(f901,plain,
    ( ~ v1_xboole_0(sK6(k1_xboole_0))
    | ~ spl8_129 ),
    inference(avatar_component_clause,[],[f900])).

fof(f918,plain,
    ( ~ spl8_131
    | spl8_129 ),
    inference(avatar_split_clause,[],[f907,f900,f916])).

fof(f907,plain,
    ( ~ r2_hidden(sK6(k1_xboole_0),sK6(sK6(k1_xboole_0)))
    | ~ spl8_129 ),
    inference(unit_resulting_resolution,[],[f85,f901,f123])).

fof(f905,plain,
    ( ~ spl8_127
    | spl8_128
    | spl8_119 ),
    inference(avatar_split_clause,[],[f869,f866,f903,f897])).

fof(f897,plain,
    ( spl8_127
  <=> ~ m1_subset_1(k1_xboole_0,sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).

fof(f903,plain,
    ( spl8_128
  <=> v1_xboole_0(sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).

fof(f866,plain,
    ( spl8_119
  <=> ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f869,plain,
    ( v1_xboole_0(sK6(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,sK6(k1_xboole_0))
    | ~ spl8_119 ),
    inference(resolution,[],[f867,f90])).

fof(f867,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0))
    | ~ spl8_119 ),
    inference(avatar_component_clause,[],[f866])).

fof(f889,plain,
    ( ~ spl8_123
    | spl8_124
    | spl8_32
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f233,f230,f266,f887,f881])).

fof(f881,plain,
    ( spl8_123
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).

fof(f266,plain,
    ( spl8_32
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f233,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_26 ),
    inference(resolution,[],[f231,f124])).

fof(f876,plain,
    ( spl8_120
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f815,f781,f874])).

fof(f874,plain,
    ( spl8_120
  <=> k1_xboole_0 = sK6(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f781,plain,
    ( spl8_106
  <=> v1_xboole_0(sK6(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).

fof(f815,plain,
    ( k1_xboole_0 = sK6(u1_struct_0(sK2))
    | ~ spl8_106 ),
    inference(unit_resulting_resolution,[],[f782,f74])).

fof(f782,plain,
    ( v1_xboole_0(sK6(u1_struct_0(sK2)))
    | ~ spl8_106 ),
    inference(avatar_component_clause,[],[f781])).

fof(f868,plain,
    ( ~ spl8_119
    | ~ spl8_106
    | spl8_109 ),
    inference(avatar_split_clause,[],[f821,f798,f781,f866])).

fof(f821,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0))
    | ~ spl8_106
    | ~ spl8_109 ),
    inference(backward_demodulation,[],[f815,f799])).

fof(f854,plain,
    ( spl8_116
    | ~ spl8_112 ),
    inference(avatar_split_clause,[],[f835,f832,f852])).

fof(f835,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_112 ),
    inference(unit_resulting_resolution,[],[f833,f89])).

fof(f847,plain,
    ( ~ spl8_115
    | spl8_105
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f822,f781,f775,f845])).

fof(f845,plain,
    ( spl8_115
  <=> ~ m1_subset_1(u1_struct_0(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f775,plain,
    ( spl8_105
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK6(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f822,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_xboole_0)
    | ~ spl8_105
    | ~ spl8_106 ),
    inference(backward_demodulation,[],[f815,f776])).

fof(f776,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),sK6(u1_struct_0(sK2)))
    | ~ spl8_105 ),
    inference(avatar_component_clause,[],[f775])).

fof(f834,plain,
    ( spl8_112
    | ~ spl8_88
    | ~ spl8_106 ),
    inference(avatar_split_clause,[],[f823,f781,f659,f832])).

fof(f659,plain,
    ( spl8_88
  <=> r2_hidden(sK6(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f823,plain,
    ( r2_hidden(k1_xboole_0,u1_struct_0(sK2))
    | ~ spl8_88
    | ~ spl8_106 ),
    inference(backward_demodulation,[],[f815,f660])).

fof(f660,plain,
    ( r2_hidden(sK6(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f659])).

fof(f807,plain,
    ( spl8_110
    | spl8_107 ),
    inference(avatar_split_clause,[],[f790,f778,f805])).

fof(f805,plain,
    ( spl8_110
  <=> r2_hidden(sK6(sK6(u1_struct_0(sK2))),sK6(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f778,plain,
    ( spl8_107
  <=> ~ v1_xboole_0(sK6(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f790,plain,
    ( r2_hidden(sK6(sK6(u1_struct_0(sK2))),sK6(u1_struct_0(sK2)))
    | ~ spl8_107 ),
    inference(unit_resulting_resolution,[],[f85,f779,f90])).

fof(f779,plain,
    ( ~ v1_xboole_0(sK6(u1_struct_0(sK2)))
    | ~ spl8_107 ),
    inference(avatar_component_clause,[],[f778])).

fof(f800,plain,
    ( ~ spl8_109
    | spl8_107 ),
    inference(avatar_split_clause,[],[f789,f778,f798])).

fof(f789,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK2)),sK6(sK6(u1_struct_0(sK2))))
    | ~ spl8_107 ),
    inference(unit_resulting_resolution,[],[f85,f779,f123])).

fof(f783,plain,
    ( ~ spl8_105
    | spl8_106
    | spl8_87 ),
    inference(avatar_split_clause,[],[f662,f647,f781,f775])).

fof(f647,plain,
    ( spl8_87
  <=> ~ r2_hidden(u1_struct_0(sK2),sK6(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f662,plain,
    ( v1_xboole_0(sK6(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK2),sK6(u1_struct_0(sK2)))
    | ~ spl8_87 ),
    inference(resolution,[],[f648,f90])).

fof(f648,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK6(u1_struct_0(sK2)))
    | ~ spl8_87 ),
    inference(avatar_component_clause,[],[f647])).

fof(f756,plain,
    ( spl8_102
    | ~ spl8_26
    | spl8_33 ),
    inference(avatar_split_clause,[],[f709,f263,f230,f754])).

fof(f754,plain,
    ( spl8_102
  <=> r2_hidden(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f709,plain,
    ( r2_hidden(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_26
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f264,f231,f90])).

fof(f749,plain,
    ( ~ spl8_101
    | ~ spl8_26
    | spl8_33 ),
    inference(avatar_split_clause,[],[f708,f263,f230,f747])).

fof(f747,plain,
    ( spl8_101
  <=> ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f708,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_26
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f264,f231,f123])).

fof(f724,plain,
    ( spl8_98
    | spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | spl8_39
    | spl8_79 ),
    inference(avatar_split_clause,[],[f678,f587,f326,f146,f105,f98,f722])).

fof(f722,plain,
    ( spl8_98
  <=> r1_lattice3(sK2,k1_xboole_0,sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).

fof(f678,plain,
    ( r1_lattice3(sK2,k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_39
    | ~ spl8_79 ),
    inference(unit_resulting_resolution,[],[f99,f106,f327,f147,f588,f80])).

fof(f703,plain,
    ( spl8_96
    | spl8_33
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f653,f631,f263,f701])).

fof(f701,plain,
    ( spl8_96
  <=> r2_hidden(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).

fof(f653,plain,
    ( r2_hidden(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_33
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f264,f632,f90])).

fof(f696,plain,
    ( ~ spl8_95
    | spl8_33
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f652,f631,f263,f694])).

fof(f694,plain,
    ( spl8_95
  <=> ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).

fof(f652,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_33
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f264,f632,f123])).

fof(f689,plain,
    ( ~ spl8_93
    | spl8_33
    | spl8_63
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f651,f631,f445,f263,f687])).

fof(f687,plain,
    ( spl8_93
  <=> ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f445,plain,
    ( spl8_63
  <=> ~ v1_xboole_0(sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f651,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_33
    | ~ spl8_63
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f264,f446,f632,f124])).

fof(f446,plain,
    ( ~ v1_xboole_0(sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f445])).

fof(f675,plain,
    ( ~ spl8_91
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f529,f457,f673])).

fof(f673,plain,
    ( spl8_91
  <=> ~ r2_hidden(sK4(sK2,sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f457,plain,
    ( spl8_64
  <=> r2_hidden(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f529,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_64 ),
    inference(resolution,[],[f458,f88])).

fof(f458,plain,
    ( r2_hidden(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f457])).

fof(f661,plain,
    ( spl8_88
    | spl8_33 ),
    inference(avatar_split_clause,[],[f615,f263,f659])).

fof(f615,plain,
    ( r2_hidden(sK6(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f85,f264,f90])).

fof(f649,plain,
    ( ~ spl8_87
    | spl8_33 ),
    inference(avatar_split_clause,[],[f614,f263,f647])).

fof(f614,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK6(u1_struct_0(sK2)))
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f85,f264,f123])).

fof(f641,plain,
    ( ~ spl8_85
    | spl8_57 ),
    inference(avatar_split_clause,[],[f426,f416,f639])).

fof(f639,plain,
    ( spl8_85
  <=> ~ r2_hidden(sK5(sK2,sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f416,plain,
    ( spl8_57
  <=> ~ m1_subset_1(sK5(sK2,sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f426,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_57 ),
    inference(resolution,[],[f417,f89])).

fof(f417,plain,
    ( ~ m1_subset_1(sK5(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f416])).

fof(f633,plain,
    ( spl8_82
    | spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | spl8_39 ),
    inference(avatar_split_clause,[],[f336,f326,f146,f105,f98,f631])).

fof(f336,plain,
    ( m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_39 ),
    inference(unit_resulting_resolution,[],[f99,f106,f147,f327,f79])).

fof(f612,plain,
    ( ~ spl8_81
    | spl8_71 ),
    inference(avatar_split_clause,[],[f512,f502,f610])).

fof(f610,plain,
    ( spl8_81
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f502,plain,
    ( spl8_71
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f512,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl8_71 ),
    inference(resolution,[],[f503,f89])).

fof(f503,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_71 ),
    inference(avatar_component_clause,[],[f502])).

fof(f602,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | spl8_39
    | ~ spl8_46
    | ~ spl8_50
    | ~ spl8_78 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_39
    | ~ spl8_46
    | ~ spl8_50
    | ~ spl8_78 ),
    inference(subsumption_resolution,[],[f600,f393])).

fof(f393,plain,
    ( m1_subset_1(sK4(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl8_50
  <=> m1_subset_1(sK4(sK2,sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f600,plain,
    ( ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_39
    | ~ spl8_46
    | ~ spl8_78 ),
    inference(forward_demodulation,[],[f599,f371])).

fof(f371,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl8_46
  <=> u1_struct_0(sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f599,plain,
    ( ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_39
    | ~ spl8_46
    | ~ spl8_78 ),
    inference(subsumption_resolution,[],[f598,f593])).

fof(f593,plain,
    ( ~ r1_lattice3(sK2,k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_39
    | ~ spl8_78 ),
    inference(unit_resulting_resolution,[],[f99,f106,f147,f327,f591,f81])).

fof(f591,plain,
    ( r1_lattice3(sK2,sK3,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl8_78
  <=> r1_lattice3(sK2,sK3,sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f598,plain,
    ( r1_lattice3(sK2,k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_46
    | ~ spl8_78 ),
    inference(forward_demodulation,[],[f597,f73])).

fof(f597,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,k1_xboole_0),sK4(sK2,sK3,k1_xboole_0))
    | ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_46
    | ~ spl8_78 ),
    inference(forward_demodulation,[],[f596,f371])).

fof(f596,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k1_xboole_0))
    | ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_78 ),
    inference(subsumption_resolution,[],[f595,f99])).

fof(f595,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k1_xboole_0))
    | ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl8_2
    | ~ spl8_78 ),
    inference(subsumption_resolution,[],[f594,f106])).

fof(f594,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k1_xboole_0))
    | ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_78 ),
    inference(resolution,[],[f591,f77])).

fof(f592,plain,
    ( spl8_78
    | spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | spl8_39
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f575,f370,f326,f146,f105,f98,f590])).

fof(f575,plain,
    ( r1_lattice3(sK2,sK3,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f147,f574])).

fof(f574,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,X0,sK4(sK2,X0,k1_xboole_0))
        | ~ r2_yellow_0(sK2,X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f573,f435])).

fof(f435,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK2,X0,k1_xboole_0),k1_xboole_0)
        | ~ r2_yellow_0(sK2,X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(resolution,[],[f380,f327])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( r2_yellow_0(sK2,X1)
        | ~ r2_yellow_0(sK2,X0)
        | m1_subset_1(sK4(sK2,X0,X1),k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f379,f99])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK2,X0,X1),k1_xboole_0)
        | ~ r2_yellow_0(sK2,X0)
        | r2_yellow_0(sK2,X1)
        | v2_struct_0(sK2) )
    | ~ spl8_2
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f378,f106])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK2,X0,X1),k1_xboole_0)
        | ~ r2_yellow_0(sK2,X0)
        | r2_yellow_0(sK2,X1)
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_46 ),
    inference(superposition,[],[f79,f371])).

fof(f573,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,X0,sK4(sK2,X0,k1_xboole_0))
        | ~ r2_yellow_0(sK2,X0)
        | ~ m1_subset_1(sK4(sK2,X0,k1_xboole_0),k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(condensation,[],[f568])).

fof(f568,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK2,X0,sK4(sK2,X0,k1_xboole_0))
        | ~ r2_yellow_0(sK2,X0)
        | ~ m1_subset_1(sK4(sK2,X0,k1_xboole_0),k1_xboole_0)
        | r1_lattice3(sK2,X1,sK4(sK2,X0,k1_xboole_0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(resolution,[],[f531,f377])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK2,k1_xboole_0,X1)
        | ~ m1_subset_1(X1,k1_xboole_0)
        | r1_lattice3(sK2,X0,X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f376,f371])).

fof(f376,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK2,k1_xboole_0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_lattice3(sK2,X0,X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f375,f73])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK2,k3_xboole_0(X0,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_lattice3(sK2,X0,X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f374,f371])).

fof(f531,plain,
    ( ! [X0] :
        ( r1_lattice3(sK2,k1_xboole_0,sK4(sK2,X0,k1_xboole_0))
        | r1_lattice3(sK2,X0,sK4(sK2,X0,k1_xboole_0))
        | ~ r2_yellow_0(sK2,X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_39 ),
    inference(resolution,[],[f400,f327])).

fof(f567,plain,
    ( ~ spl8_77
    | spl8_75 ),
    inference(avatar_split_clause,[],[f556,f545,f565])).

fof(f565,plain,
    ( spl8_77
  <=> ~ r2_hidden(sK6(sK4(sK2,sK3,k1_xboole_0)),sK6(sK6(sK4(sK2,sK3,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f556,plain,
    ( ~ r2_hidden(sK6(sK4(sK2,sK3,k1_xboole_0)),sK6(sK6(sK4(sK2,sK3,k1_xboole_0))))
    | ~ spl8_75 ),
    inference(unit_resulting_resolution,[],[f85,f546,f123])).

fof(f550,plain,
    ( ~ spl8_73
    | spl8_74
    | spl8_67 ),
    inference(avatar_split_clause,[],[f530,f469,f548,f542])).

fof(f542,plain,
    ( spl8_73
  <=> ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),sK6(sK4(sK2,sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f548,plain,
    ( spl8_74
  <=> v1_xboole_0(sK6(sK4(sK2,sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f469,plain,
    ( spl8_67
  <=> ~ r2_hidden(sK4(sK2,sK3,k1_xboole_0),sK6(sK4(sK2,sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f530,plain,
    ( v1_xboole_0(sK6(sK4(sK2,sK3,k1_xboole_0)))
    | ~ m1_subset_1(sK4(sK2,sK3,k1_xboole_0),sK6(sK4(sK2,sK3,k1_xboole_0)))
    | ~ spl8_67 ),
    inference(resolution,[],[f470,f90])).

fof(f470,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,k1_xboole_0),sK6(sK4(sK2,sK3,k1_xboole_0)))
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f469])).

fof(f510,plain,
    ( ~ spl8_60
    | spl8_63
    | spl8_65 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl8_60
    | ~ spl8_63
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f446,f508])).

fof(f508,plain,
    ( v1_xboole_0(sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_60
    | ~ spl8_65 ),
    inference(subsumption_resolution,[],[f464,f440])).

fof(f440,plain,
    ( m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl8_60
  <=> m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f464,plain,
    ( v1_xboole_0(sK4(sK2,sK3,k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_65 ),
    inference(resolution,[],[f461,f90])).

fof(f461,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl8_65
  <=> ~ r2_hidden(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f507,plain,
    ( spl8_70
    | ~ spl8_50
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f493,f448,f392,f505])).

fof(f505,plain,
    ( spl8_70
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f448,plain,
    ( spl8_62
  <=> v1_xboole_0(sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f493,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_50
    | ~ spl8_62 ),
    inference(backward_demodulation,[],[f484,f393])).

fof(f484,plain,
    ( k1_xboole_0 = sK4(sK2,sK3,k1_xboole_0)
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f449,f74])).

fof(f449,plain,
    ( v1_xboole_0(sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f448])).

fof(f495,plain,
    ( ~ spl8_50
    | spl8_61
    | ~ spl8_62 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl8_50
    | ~ spl8_61
    | ~ spl8_62 ),
    inference(subsumption_resolution,[],[f493,f492])).

fof(f492,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_61
    | ~ spl8_62 ),
    inference(backward_demodulation,[],[f484,f443])).

fof(f443,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_61 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl8_61
  <=> ~ m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f478,plain,
    ( spl8_68
    | spl8_63 ),
    inference(avatar_split_clause,[],[f453,f445,f476])).

fof(f476,plain,
    ( spl8_68
  <=> r2_hidden(sK6(sK4(sK2,sK3,k1_xboole_0)),sK4(sK2,sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f453,plain,
    ( r2_hidden(sK6(sK4(sK2,sK3,k1_xboole_0)),sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_63 ),
    inference(unit_resulting_resolution,[],[f85,f446,f90])).

fof(f471,plain,
    ( ~ spl8_67
    | spl8_63 ),
    inference(avatar_split_clause,[],[f452,f445,f469])).

fof(f452,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,k1_xboole_0),sK6(sK4(sK2,sK3,k1_xboole_0)))
    | ~ spl8_63 ),
    inference(unit_resulting_resolution,[],[f85,f446,f123])).

fof(f462,plain,
    ( ~ spl8_65
    | spl8_61 ),
    inference(avatar_split_clause,[],[f454,f442,f460])).

fof(f454,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_61 ),
    inference(unit_resulting_resolution,[],[f443,f89])).

fof(f450,plain,
    ( ~ spl8_61
    | spl8_36
    | spl8_62
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f305,f266,f230,f448,f319,f442])).

fof(f305,plain,
    ( v1_xboole_0(sK4(sK2,sK3,k1_xboole_0))
    | v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f304,f73])).

fof(f304,plain,
    ( v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,k1_xboole_0)))
    | v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f303,f275])).

fof(f275,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f267,f74])).

fof(f267,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f266])).

fof(f303,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f302,f275])).

fof(f302,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k1_xboole_0))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f288,f73])).

fof(f288,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK4(sK2,sK3,k3_xboole_0(sK3,k1_xboole_0)))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f233])).

fof(f433,plain,
    ( ~ spl8_59
    | spl8_31
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f307,f266,f250,f431])).

fof(f431,plain,
    ( spl8_59
  <=> ~ r2_hidden(sK5(sK2,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f307,plain,
    ( ~ r2_hidden(sK5(sK2,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f290,f73])).

fof(f290,plain,
    ( ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,k1_xboole_0),sK3),k1_xboole_0)
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f251])).

fof(f421,plain,
    ( spl8_56
    | spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_32
    | spl8_41 ),
    inference(avatar_split_clause,[],[f349,f339,f266,f160,f105,f98,f419])).

fof(f419,plain,
    ( spl8_56
  <=> m1_subset_1(sK5(sK2,sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f349,plain,
    ( m1_subset_1(sK5(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_32
    | ~ spl8_41 ),
    inference(forward_demodulation,[],[f347,f275])).

fof(f347,plain,
    ( m1_subset_1(sK5(sK2,sK3,k1_xboole_0),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f99,f106,f161,f340,f82])).

fof(f414,plain,
    ( ~ spl8_55
    | spl8_29
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f306,f266,f238,f412])).

fof(f412,plain,
    ( spl8_55
  <=> ~ r2_hidden(sK4(sK2,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f306,plain,
    ( ~ r2_hidden(sK4(sK2,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f289,f73])).

fof(f289,plain,
    ( ~ r2_hidden(sK4(sK2,k3_xboole_0(sK3,k1_xboole_0),sK3),k1_xboole_0)
    | ~ spl8_29
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f239])).

fof(f407,plain,
    ( ~ spl8_53
    | spl8_25
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f300,f266,f215,f405])).

fof(f405,plain,
    ( spl8_53
  <=> ~ m1_subset_1(sK5(sK2,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f215,plain,
    ( spl8_25
  <=> ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f300,plain,
    ( ~ m1_subset_1(sK5(sK2,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl8_25
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f285,f73])).

fof(f285,plain,
    ( ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,k1_xboole_0),sK3),k1_xboole_0)
    | ~ spl8_25
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f216])).

fof(f216,plain,
    ( ~ m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f215])).

fof(f394,plain,
    ( spl8_50
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f301,f266,f230,f392])).

fof(f301,plain,
    ( m1_subset_1(sK4(sK2,sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f287,f73])).

fof(f287,plain,
    ( m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_26
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f231])).

fof(f387,plain,
    ( ~ spl8_49
    | spl8_21
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f297,f266,f187,f385])).

fof(f385,plain,
    ( spl8_49
  <=> ~ m1_subset_1(sK4(sK2,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f187,plain,
    ( spl8_21
  <=> ~ m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f297,plain,
    ( ~ m1_subset_1(sK4(sK2,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl8_21
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f282,f73])).

fof(f282,plain,
    ( ~ m1_subset_1(sK4(sK2,k3_xboole_0(sK3,k1_xboole_0),sK3),k1_xboole_0)
    | ~ spl8_21
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f188])).

fof(f188,plain,
    ( ~ m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f372,plain,
    ( spl8_46
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f275,f266,f370])).

fof(f363,plain,
    ( ~ spl8_45
    | spl8_23
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f299,f266,f207,f361])).

fof(f361,plain,
    ( spl8_45
  <=> ~ sP1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f207,plain,
    ( spl8_23
  <=> ~ sP1(k3_xboole_0(sK3,u1_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f299,plain,
    ( ~ sP1(k1_xboole_0,sK2)
    | ~ spl8_23
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f284,f73])).

fof(f284,plain,
    ( ~ sP1(k3_xboole_0(sK3,k1_xboole_0),sK2)
    | ~ spl8_23
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f208])).

fof(f208,plain,
    ( ~ sP1(k3_xboole_0(sK3,u1_struct_0(sK2)),sK2)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f207])).

fof(f356,plain,
    ( ~ spl8_43
    | spl8_19
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f296,f266,f180,f354])).

fof(f354,plain,
    ( spl8_43
  <=> ~ sP0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f180,plain,
    ( spl8_19
  <=> ~ sP0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f296,plain,
    ( ~ sP0(sK2,k1_xboole_0)
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f281,f73])).

fof(f281,plain,
    ( ~ sP0(sK2,k3_xboole_0(sK3,k1_xboole_0))
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f181])).

fof(f181,plain,
    ( ~ sP0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f180])).

fof(f344,plain,
    ( spl8_40
    | ~ spl8_16
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f295,f266,f171,f342])).

fof(f295,plain,
    ( r1_yellow_0(sK2,k1_xboole_0)
    | ~ spl8_16
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f280,f73])).

fof(f280,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,k1_xboole_0))
    | ~ spl8_16
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f172])).

fof(f328,plain,
    ( ~ spl8_39
    | spl8_13
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f294,f266,f149,f326])).

fof(f294,plain,
    ( ~ r2_yellow_0(sK2,k1_xboole_0)
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f279,f73])).

fof(f279,plain,
    ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,k1_xboole_0))
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f150])).

fof(f321,plain,
    ( spl8_36
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f293,f266,f319])).

fof(f293,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f275,f267])).

fof(f271,plain,
    ( spl8_32
    | spl8_34
    | spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f244,f160,f105,f98,f269,f266])).

fof(f244,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | v1_xboole_0(u1_struct_0(sK2))
        | v1_xboole_0(sK5(sK2,sK3,X0))
        | ~ m1_subset_1(u1_struct_0(sK2),sK5(sK2,sK3,X0)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(resolution,[],[f224,f124])).

fof(f224,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK2,sK3,X0),u1_struct_0(sK2))
        | r1_yellow_0(sK2,X0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f223,f99])).

fof(f223,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | m1_subset_1(sK5(sK2,sK3,X0),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f222,f106])).

fof(f222,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK2,X0)
        | m1_subset_1(sK5(sK2,sK3,X0),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | v2_struct_0(sK2) )
    | ~ spl8_14 ),
    inference(resolution,[],[f161,f82])).

fof(f252,plain,
    ( ~ spl8_31
    | spl8_25 ),
    inference(avatar_split_clause,[],[f242,f215,f250])).

fof(f242,plain,
    ( ~ r2_hidden(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f216,f89])).

fof(f240,plain,
    ( ~ spl8_29
    | spl8_21 ),
    inference(avatar_split_clause,[],[f211,f187,f238])).

fof(f211,plain,
    ( ~ r2_hidden(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f188,f89])).

fof(f232,plain,
    ( spl8_26
    | spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | spl8_13 ),
    inference(avatar_split_clause,[],[f225,f149,f146,f105,f98,f230])).

fof(f225,plain,
    ( m1_subset_1(sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f99,f106,f147,f150,f79])).

fof(f220,plain,
    ( spl8_24
    | spl8_1
    | ~ spl8_2
    | spl8_15
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f198,f171,f163,f105,f98,f218])).

fof(f198,plain,
    ( m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f99,f106,f164,f172,f82])).

fof(f209,plain,
    ( ~ spl8_23
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f199,f171,f207])).

fof(f199,plain,
    ( ~ sP1(k3_xboole_0(sK3,u1_struct_0(sK2)),sK2)
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f172,f64])).

fof(f192,plain,
    ( spl8_20
    | spl8_1
    | ~ spl8_2
    | spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f184,f152,f143,f105,f98,f190])).

fof(f184,plain,
    ( m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f99,f106,f144,f153,f79])).

fof(f183,plain,
    ( spl8_6
    | spl8_8
    | ~ spl8_13
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f72,f143,f149,f140,f134])).

fof(f140,plain,
    ( spl8_8
  <=> sP1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f72,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | sP1(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( ( ~ r2_yellow_0(sK2,sK3)
        & r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) )
      | ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
        & r2_yellow_0(sK2,sK3) )
      | sP1(sK3,sK2)
      | sP0(sK2,sK3) )
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_yellow_0(X0,X1)
              & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              & r2_yellow_0(X0,X1) )
            | sP1(X1,X0)
            | sP0(X0,X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r2_yellow_0(sK2,X1)
            & r2_yellow_0(sK2,k3_xboole_0(X1,u1_struct_0(sK2))) )
          | ( ~ r2_yellow_0(sK2,k3_xboole_0(X1,u1_struct_0(sK2)))
            & r2_yellow_0(sK2,X1) )
          | sP1(X1,sK2)
          | sP0(sK2,X1) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | sP1(X1,X0)
          | sP0(X0,X1) )
     => ( ( ~ r2_yellow_0(X0,sK3)
          & r2_yellow_0(X0,k3_xboole_0(sK3,u1_struct_0(X0))) )
        | ( ~ r2_yellow_0(X0,k3_xboole_0(sK3,u1_struct_0(X0)))
          & r2_yellow_0(X0,sK3) )
        | sP1(sK3,X0)
        | sP0(X0,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | sP1(X1,X0)
          | sP0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f28,f43,f42])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
             => r2_yellow_0(X0,X1) )
            & ( r2_yellow_0(X0,X1)
             => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
             => r1_yellow_0(X0,X1) )
            & ( r1_yellow_0(X0,X1)
             => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X1)
           => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
           => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',t50_yellow_0)).

fof(f182,plain,
    ( ~ spl8_19
    | spl8_17 ),
    inference(avatar_split_clause,[],[f175,f168,f180])).

fof(f175,plain,
    ( ~ sP0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f169,f65])).

fof(f173,plain,
    ( spl8_16
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f155,f140,f171])).

fof(f155,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f141,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | r1_yellow_0(X1,k3_xboole_0(X0,u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f141,plain,
    ( sP1(sK3,sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f165,plain,
    ( ~ spl8_15
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f156,f140,f163])).

fof(f156,plain,
    ( ~ r1_yellow_0(sK2,sK3)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f141,f64])).

fof(f154,plain,
    ( spl8_6
    | spl8_8
    | spl8_10
    | spl8_12 ),
    inference(avatar_split_clause,[],[f69,f152,f146,f140,f134])).

fof(f69,plain,
    ( r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,sK3)
    | sP1(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f93,f112])).

fof(f112,plain,
    ( spl8_4
  <=> l1_orders_2(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f93,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    l1_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f11,f61])).

fof(f61,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK7) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t50_yellow_0.p',existence_l1_orders_2)).

fof(f107,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f68,f105])).

fof(f68,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f67,f98])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
