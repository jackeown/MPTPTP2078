%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t28_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:55 EDT 2019

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  823 (3504 expanded)
%              Number of leaves         :  231 (1473 expanded)
%              Depth                    :   19
%              Number of atoms          : 2344 (10903 expanded)
%              Number of equality atoms :   20 (  62 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2987,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f146,f153,f160,f167,f174,f181,f188,f195,f203,f213,f220,f227,f238,f246,f254,f262,f271,f279,f286,f299,f307,f314,f323,f331,f339,f346,f353,f360,f367,f376,f384,f398,f408,f416,f431,f442,f450,f458,f469,f478,f486,f494,f501,f508,f518,f525,f541,f549,f569,f577,f585,f605,f613,f621,f632,f640,f648,f659,f667,f675,f682,f689,f696,f703,f710,f717,f726,f733,f740,f762,f781,f791,f813,f824,f832,f840,f851,f862,f870,f881,f889,f897,f911,f919,f927,f969,f976,f983,f990,f997,f1004,f1011,f1018,f1025,f1034,f1202,f1211,f1219,f1226,f1235,f1243,f1252,f1259,f1301,f1321,f1329,f1340,f1348,f1355,f1363,f1374,f1438,f1446,f1519,f1527,f1535,f1614,f1622,f1714,f1733,f1740,f1751,f1786,f1824,f1838,f1862,f1869,f1880,f1888,f1933,f1950,f1971,f2005,f2027,f2065,f2086,f2093,f2104,f2112,f2123,f2143,f2169,f2181,f2210,f2212,f2220,f2252,f2286,f2294,f2346,f2357,f2411,f2429,f2437,f2444,f2469,f2481,f2482,f2489,f2499,f2507,f2514,f2521,f2623,f2630,f2637,f2651,f2691,f2700,f2707,f2734,f2741,f2758,f2765,f2794,f2801,f2808,f2821,f2842,f2851,f2865,f2872,f2888,f2895,f2902,f2915,f2931,f2938,f2945,f2953,f2960,f2977,f2986])).

fof(f2986,plain,
    ( spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_14
    | spl14_17
    | ~ spl14_204
    | ~ spl14_340
    | ~ spl14_354 ),
    inference(avatar_contradiction_clause,[],[f2985])).

fof(f2985,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_14
    | ~ spl14_17
    | ~ spl14_204
    | ~ spl14_340
    | ~ spl14_354 ),
    inference(subsumption_resolution,[],[f2984,f2919])).

fof(f2919,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2))),sK2)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_14
    | ~ spl14_204
    | ~ spl14_340 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f187,f1251,f2740,f113])).

fof(f113,plain,(
    ! [X6,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r1_orders_2(X1,sK10(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK9(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK9(X0,X1,X2,X3))
                      & m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK10(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f80,f82,f81])).

fof(f81,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK9(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK9(X0,X1,X2,X3))
        & m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK10(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',d11_waybel_0)).

fof(f2740,plain,
    ( r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2)))
    | ~ spl14_340 ),
    inference(avatar_component_clause,[],[f2739])).

fof(f2739,plain,
    ( spl14_340
  <=> r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_340])])).

fof(f1251,plain,
    ( m1_subset_1(sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_204 ),
    inference(avatar_component_clause,[],[f1250])).

fof(f1250,plain,
    ( spl14_204
  <=> m1_subset_1(sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_204])])).

fof(f187,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl14_14
  <=> r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f180,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl14_12
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f152,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl14_5
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f145,plain,
    ( l1_struct_0(sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl14_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f138,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl14_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f2984,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2))),sK2)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_17
    | ~ spl14_204
    | ~ spl14_354 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f194,f1251,f2841,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | r2_waybel_0(X0,X1,X2)
      | ~ r1_orders_2(X1,sK7(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK7(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK8(X0,X1,X2,X5))
                      & m1_subset_1(sK8(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f75,f77,f76])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK7(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK8(X0,X1,X2,X5))
        & m1_subset_1(sK8(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
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
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',d12_waybel_0)).

fof(f2841,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2)))
    | ~ spl14_354 ),
    inference(avatar_component_clause,[],[f2840])).

fof(f2840,plain,
    ( spl14_354
  <=> r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_354])])).

fof(f194,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK2)
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl14_17
  <=> ~ r2_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f2977,plain,
    ( ~ spl14_381
    | spl14_351 ),
    inference(avatar_split_clause,[],[f2810,f2806,f2975])).

fof(f2975,plain,
    ( spl14_381
  <=> ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_381])])).

fof(f2806,plain,
    ( spl14_351
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_351])])).

fof(f2810,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl14_351 ),
    inference(unit_resulting_resolution,[],[f117,f2807,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',t4_subset)).

fof(f2807,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl14_351 ),
    inference(avatar_component_clause,[],[f2806])).

fof(f117,plain,(
    ! [X0] : m1_subset_1(sK11(X0),X0) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK11(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f22,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK11(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',existence_m1_subset_1)).

fof(f2960,plain,
    ( ~ spl14_379
    | spl14_369 ),
    inference(avatar_split_clause,[],[f2922,f2913,f2958])).

fof(f2958,plain,
    ( spl14_379
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_379])])).

fof(f2913,plain,
    ( spl14_369
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_369])])).

fof(f2922,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))))
    | ~ spl14_369 ),
    inference(unit_resulting_resolution,[],[f2914,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',t1_subset)).

fof(f2914,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))))
    | ~ spl14_369 ),
    inference(avatar_component_clause,[],[f2913])).

fof(f2953,plain,
    ( ~ spl14_377
    | spl14_263
    | ~ spl14_338 ),
    inference(avatar_split_clause,[],[f2906,f2732,f1928,f2951])).

fof(f2951,plain,
    ( spl14_377
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_377])])).

fof(f1928,plain,
    ( spl14_263
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_263])])).

fof(f2732,plain,
    ( spl14_338
  <=> m1_subset_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_338])])).

fof(f2906,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl14_263
    | ~ spl14_338 ),
    inference(unit_resulting_resolution,[],[f2733,f2858])).

fof(f2858,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(X2))))
        | ~ m1_subset_1(X2,k1_xboole_0) )
    | ~ spl14_263 ),
    inference(resolution,[],[f2367,f119])).

fof(f2367,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(X0))))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl14_263 ),
    inference(resolution,[],[f1929,f773])).

fof(f773,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK11(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f770,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',t2_subset)).

fof(f770,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK11(k1_zfmisc_1(X0)))) ) ),
    inference(subsumption_resolution,[],[f768,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',t5_subset)).

fof(f768,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK11(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK11(k1_zfmisc_1(X0))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f755,f127])).

fof(f755,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK11(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK11(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f753,f120])).

fof(f753,plain,(
    ! [X0] : ~ r2_hidden(X0,sK11(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f117,f749])).

fof(f749,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f747,f128])).

fof(f747,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f746,f127])).

fof(f746,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f745])).

fof(f745,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f542])).

fof(f542,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f264,f120])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f120,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',antisymmetry_r2_hidden)).

fof(f1929,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl14_263 ),
    inference(avatar_component_clause,[],[f1928])).

fof(f2733,plain,
    ( m1_subset_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl14_338 ),
    inference(avatar_component_clause,[],[f2732])).

fof(f2945,plain,
    ( ~ spl14_375
    | ~ spl14_266
    | ~ spl14_338 ),
    inference(avatar_split_clause,[],[f2750,f2732,f1969,f2943])).

fof(f2943,plain,
    ( spl14_375
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_375])])).

fof(f1969,plain,
    ( spl14_266
  <=> r2_hidden(sK11(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_266])])).

fof(f2750,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl14_266
    | ~ spl14_338 ),
    inference(unit_resulting_resolution,[],[f1970,f2733,f961])).

fof(f961,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,X7)
      | ~ m1_subset_1(X8,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK11(k1_zfmisc_1(X8)))) ) ),
    inference(resolution,[],[f773,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',t7_boole)).

fof(f1970,plain,
    ( r2_hidden(sK11(k1_xboole_0),k1_xboole_0)
    | ~ spl14_266 ),
    inference(avatar_component_clause,[],[f1969])).

fof(f2938,plain,
    ( ~ spl14_373
    | spl14_327 ),
    inference(avatar_split_clause,[],[f2640,f2628,f2936])).

fof(f2936,plain,
    ( spl14_373
  <=> ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_373])])).

fof(f2628,plain,
    ( spl14_327
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_327])])).

fof(f2640,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))))
    | ~ spl14_327 ),
    inference(unit_resulting_resolution,[],[f117,f2629,f127])).

fof(f2629,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))
    | ~ spl14_327 ),
    inference(avatar_component_clause,[],[f2628])).

fof(f2931,plain,
    ( ~ spl14_371
    | spl14_297 ),
    inference(avatar_split_clause,[],[f2331,f2289,f2929])).

fof(f2929,plain,
    ( spl14_371
  <=> ~ r2_hidden(sK11(k1_xboole_0),k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_371])])).

fof(f2289,plain,
    ( spl14_297
  <=> k1_xboole_0 != sK11(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_297])])).

fof(f2331,plain,
    ( ~ r2_hidden(sK11(k1_xboole_0),k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))))
    | ~ spl14_297 ),
    inference(unit_resulting_resolution,[],[f117,f2290,f1311])).

fof(f1311,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_zfmisc_1(sK11(k1_zfmisc_1(X3))))
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f962,f119])).

fof(f962,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(sK11(k1_zfmisc_1(X11))))
      | ~ m1_subset_1(X11,X10)
      | k1_xboole_0 = X10 ) ),
    inference(resolution,[],[f773,f98])).

fof(f98,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',t6_boole)).

fof(f2290,plain,
    ( k1_xboole_0 != sK11(k1_xboole_0)
    | ~ spl14_297 ),
    inference(avatar_component_clause,[],[f2289])).

fof(f2915,plain,
    ( ~ spl14_369
    | ~ spl14_266
    | spl14_357 ),
    inference(avatar_split_clause,[],[f2873,f2849,f1969,f2913])).

fof(f2849,plain,
    ( spl14_357
  <=> ~ m1_subset_1(sK11(k1_xboole_0),k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_357])])).

fof(f2873,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))))
    | ~ spl14_266
    | ~ spl14_357 ),
    inference(unit_resulting_resolution,[],[f1970,f2850,f127])).

fof(f2850,plain,
    ( ~ m1_subset_1(sK11(k1_xboole_0),k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))))
    | ~ spl14_357 ),
    inference(avatar_component_clause,[],[f2849])).

fof(f2902,plain,
    ( ~ spl14_367
    | spl14_321 ),
    inference(avatar_split_clause,[],[f2609,f2512,f2900])).

fof(f2900,plain,
    ( spl14_367
  <=> ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_367])])).

fof(f2512,plain,
    ( spl14_321
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_321])])).

fof(f2609,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(k1_xboole_0)))))))
    | ~ spl14_321 ),
    inference(unit_resulting_resolution,[],[f117,f2513,f127])).

fof(f2513,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(k1_xboole_0)))))
    | ~ spl14_321 ),
    inference(avatar_component_clause,[],[f2512])).

fof(f2895,plain,
    ( ~ spl14_365
    | spl14_319 ),
    inference(avatar_split_clause,[],[f2603,f2505,f2893])).

fof(f2893,plain,
    ( spl14_365
  <=> ~ r2_hidden(sK11(k1_xboole_0),sK11(k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_365])])).

fof(f2505,plain,
    ( spl14_319
  <=> ~ m1_subset_1(sK11(k1_xboole_0),k1_zfmisc_1(sK11(sK11(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_319])])).

fof(f2603,plain,
    ( ~ r2_hidden(sK11(k1_xboole_0),sK11(k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))))
    | ~ spl14_319 ),
    inference(unit_resulting_resolution,[],[f117,f2506,f127])).

fof(f2506,plain,
    ( ~ m1_subset_1(sK11(k1_xboole_0),k1_zfmisc_1(sK11(sK11(k1_xboole_0))))
    | ~ spl14_319 ),
    inference(avatar_component_clause,[],[f2505])).

fof(f2888,plain,
    ( ~ spl14_363
    | spl14_301 ),
    inference(avatar_split_clause,[],[f2420,f2352,f2886])).

fof(f2886,plain,
    ( spl14_363
  <=> ~ r2_hidden(sK11(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_363])])).

fof(f2352,plain,
    ( spl14_301
  <=> k1_xboole_0 != sK11(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_301])])).

fof(f2420,plain,
    ( ~ r2_hidden(sK11(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl14_301 ),
    inference(unit_resulting_resolution,[],[f117,f2353,f795])).

fof(f795,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_zfmisc_1(X3))
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f767,f119])).

fof(f767,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X11,X10)
      | k1_xboole_0 = X10 ) ),
    inference(resolution,[],[f754,f98])).

fof(f754,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f749,f120])).

fof(f2353,plain,
    ( k1_xboole_0 != sK11(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_301 ),
    inference(avatar_component_clause,[],[f2352])).

fof(f2872,plain,
    ( spl14_360
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f593,f492,f484,f236,f158,f151,f2870])).

fof(f2870,plain,
    ( spl14_360
  <=> r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK7(sK0,sK1,sK2),sK10(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_360])])).

fof(f158,plain,
    ( spl14_6
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f236,plain,
    ( spl14_26
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f484,plain,
    ( spl14_82
  <=> m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_82])])).

fof(f492,plain,
    ( spl14_84
  <=> m1_subset_1(sK10(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_84])])).

fof(f593,plain,
    ( r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK7(sK0,sK1,sK2),sK10(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f485,f493,f103])).

fof(f103,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ( ! [X3] :
                ( ~ r1_orders_2(X0,sK5(X0),X3)
                | ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
                    & r1_orders_2(X0,X4,sK6(X0,X4,X5))
                    & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f69,f72,f71,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_orders_2(X0,sK5(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X5,X4,X0] :
      ( ? [X6] :
          ( r1_orders_2(X0,X5,X6)
          & r1_orders_2(X0,X4,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
        & r1_orders_2(X0,X4,sK6(X0,X4,X5))
        & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ? [X6] :
                      ( r1_orders_2(X0,X5,X6)
                      & r1_orders_2(X0,X4,X6)
                      & m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',d5_yellow_6)).

fof(f493,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl14_84 ),
    inference(avatar_component_clause,[],[f492])).

fof(f485,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl14_82 ),
    inference(avatar_component_clause,[],[f484])).

fof(f159,plain,
    ( v7_waybel_0(sK1)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f158])).

fof(f237,plain,
    ( l1_orders_2(sK1)
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f236])).

fof(f2865,plain,
    ( ~ spl14_359
    | spl14_271 ),
    inference(avatar_split_clause,[],[f2398,f2022,f2863])).

fof(f2863,plain,
    ( spl14_359
  <=> ~ m1_subset_1(sK11(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_359])])).

fof(f2022,plain,
    ( spl14_271
  <=> ~ v1_xboole_0(sK11(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_271])])).

fof(f2398,plain,
    ( ~ m1_subset_1(sK11(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl14_271 ),
    inference(unit_resulting_resolution,[],[f117,f2023,f754])).

fof(f2023,plain,
    ( ~ v1_xboole_0(sK11(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_271 ),
    inference(avatar_component_clause,[],[f2022])).

fof(f2851,plain,
    ( ~ spl14_357
    | spl14_285 ),
    inference(avatar_split_clause,[],[f2302,f2132,f2849])).

fof(f2132,plain,
    ( spl14_285
  <=> ~ v1_xboole_0(sK11(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_285])])).

fof(f2302,plain,
    ( ~ m1_subset_1(sK11(k1_xboole_0),k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))))
    | ~ spl14_285 ),
    inference(unit_resulting_resolution,[],[f117,f2133,f773])).

fof(f2133,plain,
    ( ~ v1_xboole_0(sK11(k1_xboole_0))
    | ~ spl14_285 ),
    inference(avatar_component_clause,[],[f2132])).

fof(f2842,plain,
    ( spl14_354
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f591,f492,f484,f236,f158,f151,f2840])).

fof(f591,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f493,f485,f103])).

fof(f2821,plain,
    ( spl14_352
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f562,f492,f236,f158,f151,f2819])).

fof(f2819,plain,
    ( spl14_352
  <=> r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK10(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_352])])).

fof(f562,plain,
    ( r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK10(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f493,f493,f102])).

fof(f102,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK6(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f2808,plain,
    ( ~ spl14_351
    | ~ spl14_266
    | ~ spl14_338 ),
    inference(avatar_split_clause,[],[f2748,f2732,f1969,f2806])).

fof(f2748,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl14_266
    | ~ spl14_338 ),
    inference(unit_resulting_resolution,[],[f1970,f2733,f766])).

fof(f766,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,X7)
      | ~ m1_subset_1(X8,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8)) ) ),
    inference(resolution,[],[f754,f125])).

fof(f2801,plain,
    ( ~ spl14_349
    | spl14_263
    | ~ spl14_338 ),
    inference(avatar_split_clause,[],[f2743,f2732,f1928,f2799])).

fof(f2799,plain,
    ( spl14_349
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_349])])).

fof(f2743,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl14_263
    | ~ spl14_338 ),
    inference(unit_resulting_resolution,[],[f2733,f2474])).

fof(f2474,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X2,k1_xboole_0) )
    | ~ spl14_263 ),
    inference(resolution,[],[f2369,f119])).

fof(f2369,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X2,k1_xboole_0) )
    | ~ spl14_263 ),
    inference(resolution,[],[f1929,f754])).

fof(f2794,plain,
    ( spl14_346
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f561,f492,f484,f236,f158,f151,f2792])).

fof(f2792,plain,
    ( spl14_346
  <=> r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK7(sK0,sK1,sK2),sK10(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_346])])).

fof(f561,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK7(sK0,sK1,sK2),sK10(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f485,f493,f102])).

fof(f2765,plain,
    ( ~ spl14_345
    | spl14_263
    | ~ spl14_338 ),
    inference(avatar_split_clause,[],[f2746,f2732,f1928,f2763])).

fof(f2763,plain,
    ( spl14_345
  <=> ~ r2_hidden(k1_xboole_0,sK11(sK11(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_345])])).

fof(f2746,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(sK11(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_263
    | ~ spl14_338 ),
    inference(unit_resulting_resolution,[],[f1929,f2733,f264])).

fof(f2758,plain,
    ( spl14_342
    | spl14_263
    | ~ spl14_338 ),
    inference(avatar_split_clause,[],[f2745,f2732,f1928,f2756])).

fof(f2756,plain,
    ( spl14_342
  <=> r2_hidden(sK11(sK11(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_342])])).

fof(f2745,plain,
    ( r2_hidden(sK11(sK11(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl14_263
    | ~ spl14_338 ),
    inference(unit_resulting_resolution,[],[f1929,f2733,f120])).

fof(f2741,plain,
    ( spl14_340
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f559,f492,f484,f236,f158,f151,f2739])).

fof(f559,plain,
    ( r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f493,f485,f102])).

fof(f2734,plain,
    ( spl14_338
    | ~ spl14_334 ),
    inference(avatar_split_clause,[],[f2712,f2698,f2732])).

fof(f2698,plain,
    ( spl14_334
  <=> r2_hidden(sK11(sK11(k1_zfmisc_1(k1_xboole_0))),sK11(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_334])])).

fof(f2712,plain,
    ( m1_subset_1(sK11(sK11(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl14_334 ),
    inference(unit_resulting_resolution,[],[f117,f2699,f127])).

fof(f2699,plain,
    ( r2_hidden(sK11(sK11(k1_zfmisc_1(k1_xboole_0))),sK11(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_334 ),
    inference(avatar_component_clause,[],[f2698])).

fof(f2707,plain,
    ( ~ spl14_337
    | spl14_271 ),
    inference(avatar_split_clause,[],[f2396,f2022,f2705])).

fof(f2705,plain,
    ( spl14_337
  <=> ~ r2_hidden(sK11(k1_zfmisc_1(k1_xboole_0)),sK11(sK11(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_337])])).

fof(f2396,plain,
    ( ~ r2_hidden(sK11(k1_zfmisc_1(k1_xboole_0)),sK11(sK11(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_271 ),
    inference(unit_resulting_resolution,[],[f117,f2023,f264])).

fof(f2700,plain,
    ( spl14_334
    | spl14_271 ),
    inference(avatar_split_clause,[],[f2393,f2022,f2698])).

fof(f2393,plain,
    ( r2_hidden(sK11(sK11(k1_zfmisc_1(k1_xboole_0))),sK11(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_271 ),
    inference(unit_resulting_resolution,[],[f117,f2023,f120])).

fof(f2691,plain,
    ( spl14_332
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f558,f484,f236,f158,f151,f2689])).

fof(f2689,plain,
    ( spl14_332
  <=> r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK7(sK0,sK1,sK2),sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_332])])).

fof(f558,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK7(sK0,sK1,sK2),sK7(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f485,f485,f102])).

fof(f2651,plain,
    ( ~ spl14_331
    | spl14_327 ),
    inference(avatar_split_clause,[],[f2641,f2628,f2649])).

fof(f2649,plain,
    ( spl14_331
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_331])])).

fof(f2641,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))
    | ~ spl14_327 ),
    inference(unit_resulting_resolution,[],[f2629,f119])).

fof(f2637,plain,
    ( ~ spl14_329
    | spl14_321 ),
    inference(avatar_split_clause,[],[f2610,f2512,f2635])).

fof(f2635,plain,
    ( spl14_329
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_329])])).

fof(f2610,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(k1_xboole_0)))))
    | ~ spl14_321 ),
    inference(unit_resulting_resolution,[],[f2513,f119])).

fof(f2630,plain,
    ( ~ spl14_327
    | ~ spl14_266
    | spl14_319 ),
    inference(avatar_split_clause,[],[f2602,f2505,f1969,f2628])).

fof(f2602,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK11(sK11(k1_xboole_0)))))
    | ~ spl14_266
    | ~ spl14_319 ),
    inference(unit_resulting_resolution,[],[f1970,f2506,f127])).

fof(f2623,plain,
    ( ~ spl14_325
    | spl14_297 ),
    inference(avatar_split_clause,[],[f2329,f2289,f2621])).

fof(f2621,plain,
    ( spl14_325
  <=> ~ r2_hidden(sK11(k1_xboole_0),k1_zfmisc_1(sK11(sK11(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_325])])).

fof(f2329,plain,
    ( ~ r2_hidden(sK11(k1_xboole_0),k1_zfmisc_1(sK11(sK11(k1_xboole_0))))
    | ~ spl14_297 ),
    inference(unit_resulting_resolution,[],[f117,f2290,f795])).

fof(f2521,plain,
    ( ~ spl14_323
    | spl14_271 ),
    inference(avatar_split_clause,[],[f2397,f2022,f2519])).

fof(f2519,plain,
    ( spl14_323
  <=> ~ m1_subset_1(sK11(k1_zfmisc_1(k1_xboole_0)),sK11(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_323])])).

fof(f2397,plain,
    ( ~ m1_subset_1(sK11(k1_zfmisc_1(k1_xboole_0)),sK11(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_271 ),
    inference(unit_resulting_resolution,[],[f2023,f746])).

fof(f2514,plain,
    ( ~ spl14_321
    | spl14_263 ),
    inference(avatar_split_clause,[],[f2366,f1928,f2512])).

fof(f2366,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_zfmisc_1(sK11(k1_xboole_0)))))
    | ~ spl14_263 ),
    inference(unit_resulting_resolution,[],[f117,f1929,f773])).

fof(f2507,plain,
    ( ~ spl14_319
    | spl14_285 ),
    inference(avatar_split_clause,[],[f2301,f2132,f2505])).

fof(f2301,plain,
    ( ~ m1_subset_1(sK11(k1_xboole_0),k1_zfmisc_1(sK11(sK11(k1_xboole_0))))
    | ~ spl14_285 ),
    inference(unit_resulting_resolution,[],[f117,f2133,f754])).

fof(f2499,plain,
    ( spl14_316
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | spl14_269 ),
    inference(avatar_split_clause,[],[f2006,f2003,f179,f151,f144,f137,f2497])).

fof(f2497,plain,
    ( spl14_316
  <=> m1_subset_1(sK7(sK0,sK1,k1_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_316])])).

fof(f2003,plain,
    ( spl14_269
  <=> ~ r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_269])])).

fof(f2006,plain,
    ( m1_subset_1(sK7(sK0,sK1,k1_xboole_0),u1_struct_0(sK1))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_269 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f2004,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2004,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl14_269 ),
    inference(avatar_component_clause,[],[f2003])).

fof(f2489,plain,
    ( ~ spl14_315
    | spl14_275 ),
    inference(avatar_split_clause,[],[f2094,f2084,f2487])).

fof(f2487,plain,
    ( spl14_315
  <=> ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(sK11(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_315])])).

fof(f2084,plain,
    ( spl14_275
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_275])])).

fof(f2094,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(sK11(k1_xboole_0)))))
    | ~ spl14_275 ),
    inference(unit_resulting_resolution,[],[f117,f2085,f127])).

fof(f2085,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_xboole_0)))
    | ~ spl14_275 ),
    inference(avatar_component_clause,[],[f2084])).

fof(f2482,plain,
    ( ~ spl14_287
    | spl14_284
    | spl14_273 ),
    inference(avatar_split_clause,[],[f2066,f2063,f2135,f2141])).

fof(f2141,plain,
    ( spl14_287
  <=> ~ m1_subset_1(k1_xboole_0,sK11(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_287])])).

fof(f2135,plain,
    ( spl14_284
  <=> v1_xboole_0(sK11(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_284])])).

fof(f2063,plain,
    ( spl14_273
  <=> ~ r2_hidden(k1_xboole_0,sK11(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_273])])).

fof(f2066,plain,
    ( v1_xboole_0(sK11(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,sK11(k1_xboole_0))
    | ~ spl14_273 ),
    inference(resolution,[],[f2064,f120])).

fof(f2064,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_xboole_0))
    | ~ spl14_273 ),
    inference(avatar_component_clause,[],[f2063])).

fof(f2481,plain,
    ( spl14_312
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f592,f492,f236,f158,f151,f2479])).

fof(f2479,plain,
    ( spl14_312
  <=> r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK11(u1_struct_0(sK1)),sK10(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_312])])).

fof(f592,plain,
    ( r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK11(u1_struct_0(sK1)),sK10(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f117,f493,f103])).

fof(f2469,plain,
    ( ~ spl14_311
    | spl14_285 ),
    inference(avatar_split_clause,[],[f2299,f2132,f2467])).

fof(f2467,plain,
    ( spl14_311
  <=> ~ r2_hidden(sK11(k1_xboole_0),sK11(sK11(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_311])])).

fof(f2299,plain,
    ( ~ r2_hidden(sK11(k1_xboole_0),sK11(sK11(k1_xboole_0)))
    | ~ spl14_285 ),
    inference(unit_resulting_resolution,[],[f117,f2133,f264])).

fof(f2444,plain,
    ( spl14_308
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f589,f484,f236,f158,f151,f2442])).

fof(f2442,plain,
    ( spl14_308
  <=> r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK11(u1_struct_0(sK1)),sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_308])])).

fof(f589,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK11(u1_struct_0(sK1)),sK7(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f117,f485,f103])).

fof(f2437,plain,
    ( ~ spl14_307
    | spl14_287 ),
    inference(avatar_split_clause,[],[f2159,f2141,f2435])).

fof(f2435,plain,
    ( spl14_307
  <=> ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(sK11(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_307])])).

fof(f2159,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(sK11(k1_xboole_0))))
    | ~ spl14_287 ),
    inference(unit_resulting_resolution,[],[f117,f2142,f127])).

fof(f2142,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK11(k1_xboole_0))
    | ~ spl14_287 ),
    inference(avatar_component_clause,[],[f2141])).

fof(f2429,plain,
    ( ~ spl14_305
    | spl14_293 ),
    inference(avatar_split_clause,[],[f2253,f2250,f2427])).

fof(f2427,plain,
    ( spl14_305
  <=> ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_305])])).

fof(f2250,plain,
    ( spl14_293
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_293])])).

fof(f2253,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_293 ),
    inference(unit_resulting_resolution,[],[f117,f2251,f127])).

fof(f2251,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_293 ),
    inference(avatar_component_clause,[],[f2250])).

fof(f2411,plain,
    ( spl14_302
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f556,f492,f236,f158,f151,f2409])).

fof(f2409,plain,
    ( spl14_302
  <=> r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK11(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_302])])).

fof(f556,plain,
    ( r1_orders_2(sK1,sK10(sK0,sK1,sK2),sK6(sK1,sK10(sK0,sK1,sK2),sK11(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f493,f117,f102])).

fof(f2357,plain,
    ( spl14_300
    | ~ spl14_262
    | ~ spl14_270 ),
    inference(avatar_split_clause,[],[f2260,f2025,f1931,f2355])).

fof(f2355,plain,
    ( spl14_300
  <=> k1_xboole_0 = sK11(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_300])])).

fof(f1931,plain,
    ( spl14_262
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_262])])).

fof(f2025,plain,
    ( spl14_270
  <=> v1_xboole_0(sK11(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_270])])).

fof(f2260,plain,
    ( k1_xboole_0 = sK11(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_262
    | ~ spl14_270 ),
    inference(unit_resulting_resolution,[],[f1932,f2026,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',t8_boole)).

fof(f2026,plain,
    ( v1_xboole_0(sK11(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_270 ),
    inference(avatar_component_clause,[],[f2025])).

fof(f1932,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl14_262 ),
    inference(avatar_component_clause,[],[f1931])).

fof(f2346,plain,
    ( spl14_298
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f555,f484,f236,f158,f151,f2344])).

fof(f2344,plain,
    ( spl14_298
  <=> r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK7(sK0,sK1,sK2),sK11(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_298])])).

fof(f555,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK1,sK7(sK0,sK1,sK2),sK11(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f485,f117,f102])).

fof(f2294,plain,
    ( spl14_296
    | ~ spl14_284 ),
    inference(avatar_split_clause,[],[f2182,f2135,f2292])).

fof(f2292,plain,
    ( spl14_296
  <=> k1_xboole_0 = sK11(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_296])])).

fof(f2182,plain,
    ( k1_xboole_0 = sK11(k1_xboole_0)
    | ~ spl14_284 ),
    inference(unit_resulting_resolution,[],[f2136,f98])).

fof(f2136,plain,
    ( v1_xboole_0(sK11(k1_xboole_0))
    | ~ spl14_284 ),
    inference(avatar_component_clause,[],[f2135])).

fof(f2286,plain,
    ( ~ spl14_295
    | spl14_279
    | ~ spl14_284 ),
    inference(avatar_split_clause,[],[f2200,f2135,f2102,f2284])).

fof(f2284,plain,
    ( spl14_295
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_295])])).

fof(f2102,plain,
    ( spl14_279
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_279])])).

fof(f2200,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_279
    | ~ spl14_284 ),
    inference(backward_demodulation,[],[f2182,f2103])).

fof(f2103,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(k1_xboole_0)))
    | ~ spl14_279 ),
    inference(avatar_component_clause,[],[f2102])).

fof(f2252,plain,
    ( ~ spl14_293
    | spl14_275
    | ~ spl14_284 ),
    inference(avatar_split_clause,[],[f2197,f2135,f2084,f2250])).

fof(f2197,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_275
    | ~ spl14_284 ),
    inference(backward_demodulation,[],[f2182,f2085])).

fof(f2220,plain,
    ( spl14_262
    | ~ spl14_284 ),
    inference(avatar_split_clause,[],[f2201,f2135,f1931])).

fof(f2201,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl14_284 ),
    inference(backward_demodulation,[],[f2182,f2136])).

fof(f2212,plain,
    ( spl14_263
    | ~ spl14_284 ),
    inference(avatar_contradiction_clause,[],[f2211])).

fof(f2211,plain,
    ( $false
    | ~ spl14_263
    | ~ spl14_284 ),
    inference(subsumption_resolution,[],[f2201,f1929])).

fof(f2210,plain,
    ( ~ spl14_266
    | ~ spl14_284 ),
    inference(avatar_contradiction_clause,[],[f2209])).

fof(f2209,plain,
    ( $false
    | ~ spl14_266
    | ~ spl14_284 ),
    inference(subsumption_resolution,[],[f2194,f750])).

fof(f750,plain,(
    ! [X2] : ~ r2_hidden(X2,X2) ),
    inference(subsumption_resolution,[],[f748,f125])).

fof(f748,plain,(
    ! [X2] :
      ( v1_xboole_0(X2)
      | ~ r2_hidden(X2,X2) ) ),
    inference(resolution,[],[f746,f119])).

fof(f2194,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl14_266
    | ~ spl14_284 ),
    inference(backward_demodulation,[],[f2182,f1970])).

fof(f2181,plain,
    ( spl14_290
    | spl14_285 ),
    inference(avatar_split_clause,[],[f2144,f2132,f2179])).

fof(f2179,plain,
    ( spl14_290
  <=> r2_hidden(sK11(sK11(k1_xboole_0)),sK11(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_290])])).

fof(f2144,plain,
    ( r2_hidden(sK11(sK11(k1_xboole_0)),sK11(k1_xboole_0))
    | ~ spl14_285 ),
    inference(unit_resulting_resolution,[],[f117,f2133,f120])).

fof(f2169,plain,
    ( ~ spl14_289
    | spl14_285 ),
    inference(avatar_split_clause,[],[f2152,f2132,f2167])).

fof(f2167,plain,
    ( spl14_289
  <=> ~ m1_subset_1(sK11(k1_xboole_0),sK11(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_289])])).

fof(f2152,plain,
    ( ~ m1_subset_1(sK11(k1_xboole_0),sK11(k1_xboole_0))
    | ~ spl14_285 ),
    inference(unit_resulting_resolution,[],[f2133,f746])).

fof(f2143,plain,
    ( spl14_284
    | ~ spl14_287
    | ~ spl14_266 ),
    inference(avatar_split_clause,[],[f2051,f1969,f2141,f2135])).

fof(f2051,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK11(k1_xboole_0))
    | v1_xboole_0(sK11(k1_xboole_0))
    | ~ spl14_266 ),
    inference(resolution,[],[f1970,f264])).

fof(f2123,plain,
    ( spl14_282
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f588,f492,f236,f158,f151,f2121])).

fof(f2121,plain,
    ( spl14_282
  <=> r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK10(sK0,sK1,sK2),sK11(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_282])])).

fof(f588,plain,
    ( r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK10(sK0,sK1,sK2),sK11(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f493,f117,f103])).

fof(f2112,plain,
    ( ~ spl14_281
    | spl14_271 ),
    inference(avatar_split_clause,[],[f2074,f2022,f2110])).

fof(f2110,plain,
    ( spl14_281
  <=> ~ m1_subset_1(k1_xboole_0,sK11(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_281])])).

fof(f2074,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK11(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_271 ),
    inference(unit_resulting_resolution,[],[f117,f2023,f754])).

fof(f2104,plain,
    ( ~ spl14_279
    | spl14_275 ),
    inference(avatar_split_clause,[],[f2095,f2084,f2102])).

fof(f2095,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK11(k1_xboole_0)))
    | ~ spl14_275 ),
    inference(unit_resulting_resolution,[],[f2085,f119])).

fof(f2093,plain,
    ( spl14_276
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f587,f484,f236,f158,f151,f2091])).

fof(f2091,plain,
    ( spl14_276
  <=> r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK7(sK0,sK1,sK2),sK11(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_276])])).

fof(f587,plain,
    ( r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK7(sK0,sK1,sK2),sK11(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f485,f117,f103])).

fof(f2086,plain,
    ( ~ spl14_275
    | spl14_263 ),
    inference(avatar_split_clause,[],[f2032,f1928,f2084])).

fof(f2032,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK11(k1_xboole_0)))
    | ~ spl14_263 ),
    inference(unit_resulting_resolution,[],[f117,f1929,f754])).

fof(f2065,plain,
    ( ~ spl14_273
    | spl14_263 ),
    inference(avatar_split_clause,[],[f2030,f1928,f2063])).

fof(f2030,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_xboole_0))
    | ~ spl14_263 ),
    inference(unit_resulting_resolution,[],[f117,f1929,f264])).

fof(f2027,plain,
    ( spl14_270
    | ~ spl14_262 ),
    inference(avatar_split_clause,[],[f2007,f1931,f2025])).

fof(f2007,plain,
    ( v1_xboole_0(sK11(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_262 ),
    inference(unit_resulting_resolution,[],[f117,f1976,f120])).

fof(f1976,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK11(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_262 ),
    inference(unit_resulting_resolution,[],[f117,f1932,f128])).

fof(f2005,plain,
    ( ~ spl14_269
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_262 ),
    inference(avatar_split_clause,[],[f1995,f1931,f179,f151,f144,f137,f2003])).

fof(f1995,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_262 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f117,f1975,f109])).

fof(f109,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X5)),X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1975,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl14_262 ),
    inference(unit_resulting_resolution,[],[f1932,f125])).

fof(f1971,plain,
    ( spl14_266
    | spl14_263 ),
    inference(avatar_split_clause,[],[f1934,f1928,f1969])).

fof(f1934,plain,
    ( r2_hidden(sK11(k1_xboole_0),k1_xboole_0)
    | ~ spl14_263 ),
    inference(unit_resulting_resolution,[],[f117,f1929,f120])).

fof(f1950,plain,
    ( ~ spl14_265
    | spl14_263 ),
    inference(avatar_split_clause,[],[f1937,f1928,f1948])).

fof(f1948,plain,
    ( spl14_265
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_265])])).

fof(f1937,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl14_263 ),
    inference(unit_resulting_resolution,[],[f1929,f746])).

fof(f1933,plain,
    ( spl14_262
    | ~ spl14_240 ),
    inference(avatar_split_clause,[],[f1906,f1712,f1931])).

fof(f1712,plain,
    ( spl14_240
  <=> v1_xboole_0(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_240])])).

fof(f1906,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl14_240 ),
    inference(backward_demodulation,[],[f1889,f1713])).

fof(f1713,plain,
    ( v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ spl14_240 ),
    inference(avatar_component_clause,[],[f1712])).

fof(f1889,plain,
    ( u1_waybel_0(sK0,sK1) = k1_xboole_0
    | ~ spl14_240 ),
    inference(unit_resulting_resolution,[],[f1713,f98])).

fof(f1888,plain,
    ( spl14_260
    | ~ spl14_130
    | ~ spl14_246 ),
    inference(avatar_split_clause,[],[f1825,f1749,f708,f1886])).

fof(f1886,plain,
    ( spl14_260
  <=> m1_subset_1(sK11(u1_waybel_0(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_260])])).

fof(f708,plain,
    ( spl14_130
  <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_130])])).

fof(f1749,plain,
    ( spl14_246
  <=> r2_hidden(sK11(u1_waybel_0(sK0,sK1)),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_246])])).

fof(f1825,plain,
    ( m1_subset_1(sK11(u1_waybel_0(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl14_130
    | ~ spl14_246 ),
    inference(unit_resulting_resolution,[],[f1750,f709,f127])).

fof(f709,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_130 ),
    inference(avatar_component_clause,[],[f708])).

fof(f1750,plain,
    ( r2_hidden(sK11(u1_waybel_0(sK0,sK1)),u1_waybel_0(sK0,sK1))
    | ~ spl14_246 ),
    inference(avatar_component_clause,[],[f1749])).

fof(f1880,plain,
    ( ~ spl14_259
    | spl14_257 ),
    inference(avatar_split_clause,[],[f1871,f1867,f1878])).

fof(f1878,plain,
    ( spl14_259
  <=> ~ r2_hidden(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK11(u1_waybel_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_259])])).

fof(f1867,plain,
    ( spl14_257
  <=> ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK11(u1_waybel_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_257])])).

fof(f1871,plain,
    ( ~ r2_hidden(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK11(u1_waybel_0(sK0,sK1))))
    | ~ spl14_257 ),
    inference(unit_resulting_resolution,[],[f1868,f119])).

fof(f1868,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK11(u1_waybel_0(sK0,sK1))))
    | ~ spl14_257 ),
    inference(avatar_component_clause,[],[f1867])).

fof(f1869,plain,
    ( ~ spl14_257
    | spl14_241 ),
    inference(avatar_split_clause,[],[f1791,f1709,f1867])).

fof(f1709,plain,
    ( spl14_241
  <=> ~ v1_xboole_0(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_241])])).

fof(f1791,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK11(u1_waybel_0(sK0,sK1))))
    | ~ spl14_241 ),
    inference(unit_resulting_resolution,[],[f117,f1710,f754])).

fof(f1710,plain,
    ( ~ v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ spl14_241 ),
    inference(avatar_component_clause,[],[f1709])).

fof(f1862,plain,
    ( spl14_254
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f560,f492,f236,f158,f151,f1860])).

fof(f1860,plain,
    ( spl14_254
  <=> r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK11(u1_struct_0(sK1)),sK10(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_254])])).

fof(f560,plain,
    ( r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK11(u1_struct_0(sK1)),sK10(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f117,f493,f102])).

fof(f1838,plain,
    ( ~ spl14_253
    | ~ spl14_130
    | ~ spl14_246 ),
    inference(avatar_split_clause,[],[f1826,f1749,f708,f1836])).

fof(f1836,plain,
    ( spl14_253
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_253])])).

fof(f1826,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl14_130
    | ~ spl14_246 ),
    inference(unit_resulting_resolution,[],[f1750,f709,f128])).

fof(f1824,plain,
    ( ~ spl14_251
    | spl14_241 ),
    inference(avatar_split_clause,[],[f1789,f1709,f1822])).

fof(f1822,plain,
    ( spl14_251
  <=> ~ r2_hidden(u1_waybel_0(sK0,sK1),sK11(u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_251])])).

fof(f1789,plain,
    ( ~ r2_hidden(u1_waybel_0(sK0,sK1),sK11(u1_waybel_0(sK0,sK1)))
    | ~ spl14_241 ),
    inference(unit_resulting_resolution,[],[f117,f1710,f264])).

fof(f1786,plain,
    ( spl14_248
    | ~ spl14_42
    | ~ spl14_240 ),
    inference(avatar_split_clause,[],[f1763,f1712,f305,f1784])).

fof(f1784,plain,
    ( spl14_248
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_248])])).

fof(f305,plain,
    ( spl14_42
  <=> v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_42])])).

fof(f1763,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl14_42
    | ~ spl14_240 ),
    inference(backward_demodulation,[],[f1752,f306])).

fof(f306,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ spl14_42 ),
    inference(avatar_component_clause,[],[f305])).

fof(f1752,plain,
    ( u1_waybel_0(sK0,sK1) = k1_xboole_0
    | ~ spl14_240 ),
    inference(unit_resulting_resolution,[],[f1713,f98])).

fof(f1751,plain,
    ( spl14_246
    | spl14_241 ),
    inference(avatar_split_clause,[],[f1715,f1709,f1749])).

fof(f1715,plain,
    ( r2_hidden(sK11(u1_waybel_0(sK0,sK1)),u1_waybel_0(sK0,sK1))
    | ~ spl14_241 ),
    inference(unit_resulting_resolution,[],[f117,f1710,f120])).

fof(f1740,plain,
    ( spl14_244
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f557,f484,f236,f158,f151,f1738])).

fof(f1738,plain,
    ( spl14_244
  <=> r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK11(u1_struct_0(sK1)),sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_244])])).

fof(f557,plain,
    ( r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK11(u1_struct_0(sK1)),sK7(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f117,f485,f102])).

fof(f1733,plain,
    ( ~ spl14_243
    | spl14_241 ),
    inference(avatar_split_clause,[],[f1719,f1709,f1731])).

fof(f1731,plain,
    ( spl14_243
  <=> ~ m1_subset_1(u1_waybel_0(sK0,sK1),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_243])])).

fof(f1719,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),u1_waybel_0(sK0,sK1))
    | ~ spl14_241 ),
    inference(unit_resulting_resolution,[],[f1710,f746])).

fof(f1714,plain,
    ( ~ spl14_239
    | spl14_240
    | spl14_141 ),
    inference(avatar_split_clause,[],[f763,f760,f1712,f1706])).

fof(f1706,plain,
    ( spl14_239
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_239])])).

fof(f760,plain,
    ( spl14_141
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_141])])).

fof(f763,plain,
    ( v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1))
    | ~ spl14_141 ),
    inference(resolution,[],[f761,f120])).

fof(f761,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1))
    | ~ spl14_141 ),
    inference(avatar_component_clause,[],[f760])).

fof(f1622,plain,
    ( spl14_236
    | ~ spl14_234 ),
    inference(avatar_split_clause,[],[f1615,f1612,f1620])).

fof(f1620,plain,
    ( spl14_236
  <=> l1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_236])])).

fof(f1612,plain,
    ( spl14_234
  <=> l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_234])])).

fof(f1615,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl14_234 ),
    inference(unit_resulting_resolution,[],[f1613,f97])).

fof(f97,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',dt_l1_orders_2)).

fof(f1613,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl14_234 ),
    inference(avatar_component_clause,[],[f1612])).

fof(f1614,plain,
    ( spl14_234
    | ~ spl14_168
    | ~ spl14_232 ),
    inference(avatar_split_clause,[],[f1604,f1533,f917,f1612])).

fof(f917,plain,
    ( spl14_168
  <=> l1_struct_0(sK3(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_168])])).

fof(f1533,plain,
    ( spl14_232
  <=> l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK1))))),sK3(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_232])])).

fof(f1604,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl14_168
    | ~ spl14_232 ),
    inference(unit_resulting_resolution,[],[f918,f1534,f99])).

fof(f99,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',dt_l1_waybel_0)).

fof(f1534,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK1))))),sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl14_232 ),
    inference(avatar_component_clause,[],[f1533])).

fof(f918,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl14_168 ),
    inference(avatar_component_clause,[],[f917])).

fof(f1535,plain,
    ( spl14_232
    | ~ spl14_168 ),
    inference(avatar_split_clause,[],[f920,f917,f1533])).

fof(f920,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK1))))),sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl14_168 ),
    inference(unit_resulting_resolution,[],[f918,f100])).

fof(f100,plain,(
    ! [X0] :
      ( l1_waybel_0(sK3(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_waybel_0(sK3(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',existence_l1_waybel_0)).

fof(f1527,plain,
    ( spl14_230
    | ~ spl14_228 ),
    inference(avatar_split_clause,[],[f1520,f1517,f1525])).

fof(f1525,plain,
    ( spl14_230
  <=> l1_struct_0(sK3(sK3(sK3(sK3(sK3(sK12)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_230])])).

fof(f1517,plain,
    ( spl14_228
  <=> l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK12)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_228])])).

fof(f1520,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK3(sK12))))))
    | ~ spl14_228 ),
    inference(unit_resulting_resolution,[],[f1518,f97])).

fof(f1518,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK12))))))
    | ~ spl14_228 ),
    inference(avatar_component_clause,[],[f1517])).

fof(f1519,plain,
    ( spl14_228
    | ~ spl14_162
    | ~ spl14_226 ),
    inference(avatar_split_clause,[],[f1447,f1444,f887,f1517])).

fof(f887,plain,
    ( spl14_162
  <=> l1_struct_0(sK3(sK3(sK3(sK3(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_162])])).

fof(f1444,plain,
    ( spl14_226
  <=> l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK12))))),sK3(sK3(sK3(sK3(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_226])])).

fof(f1447,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK12))))))
    | ~ spl14_162
    | ~ spl14_226 ),
    inference(unit_resulting_resolution,[],[f888,f1445,f99])).

fof(f1445,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK12))))),sK3(sK3(sK3(sK3(sK12)))))
    | ~ spl14_226 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f888,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK12)))))
    | ~ spl14_162 ),
    inference(avatar_component_clause,[],[f887])).

fof(f1446,plain,
    ( spl14_226
    | ~ spl14_162 ),
    inference(avatar_split_clause,[],[f890,f887,f1444])).

fof(f890,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK12))))),sK3(sK3(sK3(sK3(sK12)))))
    | ~ spl14_162 ),
    inference(unit_resulting_resolution,[],[f888,f100])).

fof(f1438,plain,
    ( spl14_224
    | ~ spl14_222 ),
    inference(avatar_split_clause,[],[f1431,f1372,f1436])).

fof(f1436,plain,
    ( spl14_224
  <=> l1_struct_0(sK3(sK3(sK3(sK3(sK3(sK13)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_224])])).

fof(f1372,plain,
    ( spl14_222
  <=> l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK13)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_222])])).

fof(f1431,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK3(sK13))))))
    | ~ spl14_222 ),
    inference(unit_resulting_resolution,[],[f1373,f97])).

fof(f1373,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK13))))))
    | ~ spl14_222 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1374,plain,
    ( spl14_222
    | ~ spl14_156
    | ~ spl14_220 ),
    inference(avatar_split_clause,[],[f1364,f1361,f860,f1372])).

fof(f860,plain,
    ( spl14_156
  <=> l1_struct_0(sK3(sK3(sK3(sK3(sK13))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_156])])).

fof(f1361,plain,
    ( spl14_220
  <=> l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK13))))),sK3(sK3(sK3(sK3(sK13))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_220])])).

fof(f1364,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK13))))))
    | ~ spl14_156
    | ~ spl14_220 ),
    inference(unit_resulting_resolution,[],[f861,f1362,f99])).

fof(f1362,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK13))))),sK3(sK3(sK3(sK3(sK13)))))
    | ~ spl14_220 ),
    inference(avatar_component_clause,[],[f1361])).

fof(f861,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK13)))))
    | ~ spl14_156 ),
    inference(avatar_component_clause,[],[f860])).

fof(f1363,plain,
    ( spl14_220
    | ~ spl14_156 ),
    inference(avatar_split_clause,[],[f863,f860,f1361])).

fof(f863,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK13))))),sK3(sK3(sK3(sK3(sK13)))))
    | ~ spl14_156 ),
    inference(unit_resulting_resolution,[],[f861,f100])).

fof(f1355,plain,
    ( spl14_218
    | ~ spl14_214 ),
    inference(avatar_split_clause,[],[f1341,f1338,f1353])).

fof(f1353,plain,
    ( spl14_218
  <=> l1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_218])])).

fof(f1338,plain,
    ( spl14_214
  <=> l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_214])])).

fof(f1341,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl14_214 ),
    inference(unit_resulting_resolution,[],[f1339,f97])).

fof(f1339,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl14_214 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1348,plain,
    ( spl14_216
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f554,f236,f158,f151,f1346])).

fof(f1346,plain,
    ( spl14_216
  <=> r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK11(u1_struct_0(sK1)),sK11(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_216])])).

fof(f554,plain,
    ( r1_orders_2(sK1,sK11(u1_struct_0(sK1)),sK6(sK1,sK11(u1_struct_0(sK1)),sK11(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f117,f117,f102])).

fof(f1340,plain,
    ( spl14_214
    | ~ spl14_150
    | ~ spl14_212 ),
    inference(avatar_split_clause,[],[f1330,f1327,f830,f1338])).

fof(f830,plain,
    ( spl14_150
  <=> l1_struct_0(sK3(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_150])])).

fof(f1327,plain,
    ( spl14_212
  <=> l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK0))))),sK3(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_212])])).

fof(f1330,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl14_150
    | ~ spl14_212 ),
    inference(unit_resulting_resolution,[],[f831,f1328,f99])).

fof(f1328,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK0))))),sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl14_212 ),
    inference(avatar_component_clause,[],[f1327])).

fof(f831,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl14_150 ),
    inference(avatar_component_clause,[],[f830])).

fof(f1329,plain,
    ( spl14_212
    | ~ spl14_150 ),
    inference(avatar_split_clause,[],[f833,f830,f1327])).

fof(f833,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK3(sK0))))),sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl14_150 ),
    inference(unit_resulting_resolution,[],[f831,f100])).

fof(f1321,plain,
    ( spl14_210
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f534,f492,f236,f158,f151,f1319])).

fof(f1319,plain,
    ( spl14_210
  <=> m1_subset_1(sK6(sK1,sK10(sK0,sK1,sK2),sK10(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_210])])).

fof(f534,plain,
    ( m1_subset_1(sK6(sK1,sK10(sK0,sK1,sK2),sK10(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f493,f493,f101])).

fof(f101,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1301,plain,
    ( spl14_208
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f533,f492,f484,f236,f158,f151,f1299])).

fof(f1299,plain,
    ( spl14_208
  <=> m1_subset_1(sK6(sK1,sK7(sK0,sK1,sK2),sK10(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_208])])).

fof(f533,plain,
    ( m1_subset_1(sK6(sK1,sK7(sK0,sK1,sK2),sK10(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f485,f493,f101])).

fof(f1259,plain,
    ( ~ spl14_207
    | ~ spl14_202 ),
    inference(avatar_split_clause,[],[f1244,f1241,f1257])).

fof(f1257,plain,
    ( spl14_207
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK1)),u1_waybel_0(sK1,sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_207])])).

fof(f1241,plain,
    ( spl14_202
  <=> m1_subset_1(u1_waybel_0(sK1,sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_202])])).

fof(f1244,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK1)),u1_waybel_0(sK1,sK3(sK1)))
    | ~ spl14_202 ),
    inference(unit_resulting_resolution,[],[f1242,f749])).

fof(f1242,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK1))))
    | ~ spl14_202 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1252,plain,
    ( spl14_204
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f531,f492,f484,f236,f158,f151,f1250])).

fof(f531,plain,
    ( m1_subset_1(sK6(sK1,sK10(sK0,sK1,sK2),sK7(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f493,f485,f101])).

fof(f1243,plain,
    ( spl14_202
    | ~ spl14_28
    | ~ spl14_44 ),
    inference(avatar_split_clause,[],[f419,f312,f244,f1241])).

fof(f244,plain,
    ( spl14_28
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f312,plain,
    ( spl14_44
  <=> l1_waybel_0(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_44])])).

fof(f419,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK1))))
    | ~ spl14_28
    | ~ spl14_44 ),
    inference(unit_resulting_resolution,[],[f245,f313,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',dt_u1_waybel_0)).

fof(f313,plain,
    ( l1_waybel_0(sK3(sK1),sK1)
    | ~ spl14_44 ),
    inference(avatar_component_clause,[],[f312])).

fof(f245,plain,
    ( l1_struct_0(sK1)
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f1235,plain,
    ( ~ spl14_201
    | ~ spl14_196 ),
    inference(avatar_split_clause,[],[f1227,f1217,f1233])).

fof(f1233,plain,
    ( spl14_201
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK3(sK12)),u1_struct_0(sK12)),u1_waybel_0(sK12,sK3(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_201])])).

fof(f1217,plain,
    ( spl14_196
  <=> m1_subset_1(u1_waybel_0(sK12,sK3(sK12)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK12)),u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_196])])).

fof(f1227,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK3(sK12)),u1_struct_0(sK12)),u1_waybel_0(sK12,sK3(sK12)))
    | ~ spl14_196 ),
    inference(unit_resulting_resolution,[],[f1218,f749])).

fof(f1218,plain,
    ( m1_subset_1(u1_waybel_0(sK12,sK3(sK12)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK12)),u1_struct_0(sK12))))
    | ~ spl14_196 ),
    inference(avatar_component_clause,[],[f1217])).

fof(f1226,plain,
    ( spl14_198
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f530,f484,f236,f158,f151,f1224])).

fof(f1224,plain,
    ( spl14_198
  <=> m1_subset_1(sK6(sK1,sK7(sK0,sK1,sK2),sK7(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_198])])).

fof(f530,plain,
    ( m1_subset_1(sK6(sK1,sK7(sK0,sK1,sK2),sK7(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f485,f485,f101])).

fof(f1219,plain,
    ( spl14_196
    | ~ spl14_18
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f422,f225,f201,f1217])).

fof(f201,plain,
    ( spl14_18
  <=> l1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f225,plain,
    ( spl14_24
  <=> l1_waybel_0(sK3(sK12),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f422,plain,
    ( m1_subset_1(u1_waybel_0(sK12,sK3(sK12)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK12)),u1_struct_0(sK12))))
    | ~ spl14_18
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f202,f226,f123])).

fof(f226,plain,
    ( l1_waybel_0(sK3(sK12),sK12)
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f202,plain,
    ( l1_struct_0(sK12)
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1211,plain,
    ( ~ spl14_195
    | ~ spl14_192 ),
    inference(avatar_split_clause,[],[f1203,f1200,f1209])).

fof(f1209,plain,
    ( spl14_195
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK3(sK13)),u1_struct_0(sK13)),u1_waybel_0(sK13,sK3(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_195])])).

fof(f1200,plain,
    ( spl14_192
  <=> m1_subset_1(u1_waybel_0(sK13,sK3(sK13)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK13)),u1_struct_0(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_192])])).

fof(f1203,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK3(sK13)),u1_struct_0(sK13)),u1_waybel_0(sK13,sK3(sK13)))
    | ~ spl14_192 ),
    inference(unit_resulting_resolution,[],[f1201,f749])).

fof(f1201,plain,
    ( m1_subset_1(u1_waybel_0(sK13,sK3(sK13)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK13)),u1_struct_0(sK13))))
    | ~ spl14_192 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f1202,plain,
    ( spl14_192
    | ~ spl14_10
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f423,f218,f172,f1200])).

fof(f172,plain,
    ( spl14_10
  <=> l1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f218,plain,
    ( spl14_22
  <=> l1_waybel_0(sK3(sK13),sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f423,plain,
    ( m1_subset_1(u1_waybel_0(sK13,sK3(sK13)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK13)),u1_struct_0(sK13))))
    | ~ spl14_10
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f173,f219,f123])).

fof(f219,plain,
    ( l1_waybel_0(sK3(sK13),sK13)
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f173,plain,
    ( l1_struct_0(sK13)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1034,plain,
    ( ~ spl14_191
    | ~ spl14_174 ),
    inference(avatar_split_clause,[],[f1026,f974,f1032])).

fof(f1032,plain,
    ( spl14_191
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)),u1_waybel_0(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_191])])).

fof(f974,plain,
    ( spl14_174
  <=> m1_subset_1(u1_waybel_0(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_174])])).

fof(f1026,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)),u1_waybel_0(sK0,sK3(sK0)))
    | ~ spl14_174 ),
    inference(unit_resulting_resolution,[],[f975,f749])).

fof(f975,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl14_174 ),
    inference(avatar_component_clause,[],[f974])).

fof(f1025,plain,
    ( spl14_188
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f532,f492,f236,f158,f151,f1023])).

fof(f1023,plain,
    ( spl14_188
  <=> m1_subset_1(sK6(sK1,sK11(u1_struct_0(sK1)),sK10(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_188])])).

fof(f532,plain,
    ( m1_subset_1(sK6(sK1,sK11(u1_struct_0(sK1)),sK10(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f117,f493,f101])).

fof(f1018,plain,
    ( spl14_186
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f529,f484,f236,f158,f151,f1016])).

fof(f1016,plain,
    ( spl14_186
  <=> m1_subset_1(sK6(sK1,sK11(u1_struct_0(sK1)),sK7(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_186])])).

fof(f529,plain,
    ( m1_subset_1(sK6(sK1,sK11(u1_struct_0(sK1)),sK7(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f117,f485,f101])).

fof(f1011,plain,
    ( spl14_184
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f528,f492,f236,f158,f151,f1009])).

fof(f1009,plain,
    ( spl14_184
  <=> m1_subset_1(sK6(sK1,sK10(sK0,sK1,sK2),sK11(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_184])])).

fof(f528,plain,
    ( m1_subset_1(sK6(sK1,sK10(sK0,sK1,sK2),sK11(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f493,f117,f101])).

fof(f1004,plain,
    ( spl14_182
    | ~ spl14_118
    | ~ spl14_164 ),
    inference(avatar_split_clause,[],[f902,f895,f665,f1002])).

fof(f1002,plain,
    ( spl14_182
  <=> v1_funct_1(u1_waybel_0(sK3(sK3(sK3(sK1))),sK3(sK3(sK3(sK3(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_182])])).

fof(f665,plain,
    ( spl14_118
  <=> l1_struct_0(sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_118])])).

fof(f895,plain,
    ( spl14_164
  <=> l1_waybel_0(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_164])])).

fof(f902,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK3(sK3(sK1))),sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl14_118
    | ~ spl14_164 ),
    inference(unit_resulting_resolution,[],[f666,f896,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f896,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1))))
    | ~ spl14_164 ),
    inference(avatar_component_clause,[],[f895])).

fof(f666,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK1))))
    | ~ spl14_118 ),
    inference(avatar_component_clause,[],[f665])).

fof(f997,plain,
    ( spl14_180
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f527,f484,f236,f158,f151,f995])).

fof(f995,plain,
    ( spl14_180
  <=> m1_subset_1(sK6(sK1,sK7(sK0,sK1,sK2),sK11(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_180])])).

fof(f527,plain,
    ( m1_subset_1(sK6(sK1,sK7(sK0,sK1,sK2),sK11(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f485,f117,f101])).

fof(f990,plain,
    ( spl14_178
    | ~ spl14_112
    | ~ spl14_158 ),
    inference(avatar_split_clause,[],[f872,f868,f638,f988])).

fof(f988,plain,
    ( spl14_178
  <=> v1_funct_1(u1_waybel_0(sK3(sK3(sK3(sK12))),sK3(sK3(sK3(sK3(sK12)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_178])])).

fof(f638,plain,
    ( spl14_112
  <=> l1_struct_0(sK3(sK3(sK3(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_112])])).

fof(f868,plain,
    ( spl14_158
  <=> l1_waybel_0(sK3(sK3(sK3(sK3(sK12)))),sK3(sK3(sK3(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_158])])).

fof(f872,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK3(sK3(sK12))),sK3(sK3(sK3(sK3(sK12))))))
    | ~ spl14_112
    | ~ spl14_158 ),
    inference(unit_resulting_resolution,[],[f639,f869,f121])).

fof(f869,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK12)))),sK3(sK3(sK3(sK12))))
    | ~ spl14_158 ),
    inference(avatar_component_clause,[],[f868])).

fof(f639,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK12))))
    | ~ spl14_112 ),
    inference(avatar_component_clause,[],[f638])).

fof(f983,plain,
    ( spl14_176
    | ~ spl14_106
    | ~ spl14_152 ),
    inference(avatar_split_clause,[],[f842,f838,f611,f981])).

fof(f981,plain,
    ( spl14_176
  <=> v1_funct_1(u1_waybel_0(sK3(sK3(sK3(sK13))),sK3(sK3(sK3(sK3(sK13)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_176])])).

fof(f611,plain,
    ( spl14_106
  <=> l1_struct_0(sK3(sK3(sK3(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_106])])).

fof(f838,plain,
    ( spl14_152
  <=> l1_waybel_0(sK3(sK3(sK3(sK3(sK13)))),sK3(sK3(sK3(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_152])])).

fof(f842,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK3(sK3(sK13))),sK3(sK3(sK3(sK3(sK13))))))
    | ~ spl14_106
    | ~ spl14_152 ),
    inference(unit_resulting_resolution,[],[f612,f839,f121])).

fof(f839,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK13)))),sK3(sK3(sK3(sK13))))
    | ~ spl14_152 ),
    inference(avatar_component_clause,[],[f838])).

fof(f612,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK13))))
    | ~ spl14_106 ),
    inference(avatar_component_clause,[],[f611])).

fof(f976,plain,
    ( spl14_174
    | ~ spl14_2
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f418,f211,f144,f974])).

fof(f211,plain,
    ( spl14_20
  <=> l1_waybel_0(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f418,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl14_2
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f145,f212,f123])).

fof(f212,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f211])).

fof(f969,plain,
    ( spl14_172
    | ~ spl14_100
    | ~ spl14_146 ),
    inference(avatar_split_clause,[],[f815,f811,f575,f967])).

fof(f967,plain,
    ( spl14_172
  <=> v1_funct_1(u1_waybel_0(sK3(sK3(sK3(sK0))),sK3(sK3(sK3(sK3(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_172])])).

fof(f575,plain,
    ( spl14_100
  <=> l1_struct_0(sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_100])])).

fof(f811,plain,
    ( spl14_146
  <=> l1_waybel_0(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_146])])).

fof(f815,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK3(sK3(sK0))),sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl14_100
    | ~ spl14_146 ),
    inference(unit_resulting_resolution,[],[f576,f812,f121])).

fof(f812,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0))))
    | ~ spl14_146 ),
    inference(avatar_component_clause,[],[f811])).

fof(f576,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK0))))
    | ~ spl14_100 ),
    inference(avatar_component_clause,[],[f575])).

fof(f927,plain,
    ( spl14_170
    | spl14_5
    | ~ spl14_6
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f526,f236,f158,f151,f925])).

fof(f925,plain,
    ( spl14_170
  <=> m1_subset_1(sK6(sK1,sK11(u1_struct_0(sK1)),sK11(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_170])])).

fof(f526,plain,
    ( m1_subset_1(sK6(sK1,sK11(u1_struct_0(sK1)),sK11(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f152,f237,f159,f117,f117,f101])).

fof(f919,plain,
    ( spl14_168
    | ~ spl14_166 ),
    inference(avatar_split_clause,[],[f912,f909,f917])).

fof(f909,plain,
    ( spl14_166
  <=> l1_orders_2(sK3(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_166])])).

fof(f912,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl14_166 ),
    inference(unit_resulting_resolution,[],[f910,f97])).

fof(f910,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl14_166 ),
    inference(avatar_component_clause,[],[f909])).

fof(f911,plain,
    ( spl14_166
    | ~ spl14_118
    | ~ spl14_164 ),
    inference(avatar_split_clause,[],[f901,f895,f665,f909])).

fof(f901,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl14_118
    | ~ spl14_164 ),
    inference(unit_resulting_resolution,[],[f666,f896,f99])).

fof(f897,plain,
    ( spl14_164
    | ~ spl14_118 ),
    inference(avatar_split_clause,[],[f668,f665,f895])).

fof(f668,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK1)))),sK3(sK3(sK3(sK1))))
    | ~ spl14_118 ),
    inference(unit_resulting_resolution,[],[f666,f100])).

fof(f889,plain,
    ( spl14_162
    | ~ spl14_160 ),
    inference(avatar_split_clause,[],[f882,f879,f887])).

fof(f879,plain,
    ( spl14_160
  <=> l1_orders_2(sK3(sK3(sK3(sK3(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_160])])).

fof(f882,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK12)))))
    | ~ spl14_160 ),
    inference(unit_resulting_resolution,[],[f880,f97])).

fof(f880,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK12)))))
    | ~ spl14_160 ),
    inference(avatar_component_clause,[],[f879])).

fof(f881,plain,
    ( spl14_160
    | ~ spl14_112
    | ~ spl14_158 ),
    inference(avatar_split_clause,[],[f871,f868,f638,f879])).

fof(f871,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK12)))))
    | ~ spl14_112
    | ~ spl14_158 ),
    inference(unit_resulting_resolution,[],[f639,f869,f99])).

fof(f870,plain,
    ( spl14_158
    | ~ spl14_112 ),
    inference(avatar_split_clause,[],[f641,f638,f868])).

fof(f641,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK12)))),sK3(sK3(sK3(sK12))))
    | ~ spl14_112 ),
    inference(unit_resulting_resolution,[],[f639,f100])).

fof(f862,plain,
    ( spl14_156
    | ~ spl14_154 ),
    inference(avatar_split_clause,[],[f855,f849,f860])).

fof(f849,plain,
    ( spl14_154
  <=> l1_orders_2(sK3(sK3(sK3(sK3(sK13))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_154])])).

fof(f855,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK13)))))
    | ~ spl14_154 ),
    inference(unit_resulting_resolution,[],[f850,f97])).

fof(f850,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK13)))))
    | ~ spl14_154 ),
    inference(avatar_component_clause,[],[f849])).

fof(f851,plain,
    ( spl14_154
    | ~ spl14_106
    | ~ spl14_152 ),
    inference(avatar_split_clause,[],[f841,f838,f611,f849])).

fof(f841,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK13)))))
    | ~ spl14_106
    | ~ spl14_152 ),
    inference(unit_resulting_resolution,[],[f612,f839,f99])).

fof(f840,plain,
    ( spl14_152
    | ~ spl14_106 ),
    inference(avatar_split_clause,[],[f614,f611,f838])).

fof(f614,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK13)))),sK3(sK3(sK3(sK13))))
    | ~ spl14_106 ),
    inference(unit_resulting_resolution,[],[f612,f100])).

fof(f832,plain,
    ( spl14_150
    | ~ spl14_148 ),
    inference(avatar_split_clause,[],[f825,f822,f830])).

fof(f822,plain,
    ( spl14_148
  <=> l1_orders_2(sK3(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_148])])).

fof(f825,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl14_148 ),
    inference(unit_resulting_resolution,[],[f823,f97])).

fof(f823,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl14_148 ),
    inference(avatar_component_clause,[],[f822])).

fof(f824,plain,
    ( spl14_148
    | ~ spl14_100
    | ~ spl14_146 ),
    inference(avatar_split_clause,[],[f814,f811,f575,f822])).

fof(f814,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl14_100
    | ~ spl14_146 ),
    inference(unit_resulting_resolution,[],[f576,f812,f99])).

fof(f813,plain,
    ( spl14_146
    | ~ spl14_100 ),
    inference(avatar_split_clause,[],[f578,f575,f811])).

fof(f578,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK3(sK0)))),sK3(sK3(sK3(sK0))))
    | ~ spl14_100 ),
    inference(unit_resulting_resolution,[],[f576,f100])).

fof(f791,plain,
    ( spl14_144
    | ~ spl14_28
    | ~ spl14_44 ),
    inference(avatar_split_clause,[],[f388,f312,f244,f789])).

fof(f789,plain,
    ( spl14_144
  <=> v1_funct_2(u1_waybel_0(sK1,sK3(sK1)),u1_struct_0(sK3(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_144])])).

fof(f388,plain,
    ( v1_funct_2(u1_waybel_0(sK1,sK3(sK1)),u1_struct_0(sK3(sK1)),u1_struct_0(sK1))
    | ~ spl14_28
    | ~ spl14_44 ),
    inference(unit_resulting_resolution,[],[f245,f313,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f781,plain,
    ( spl14_142
    | ~ spl14_18
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f390,f225,f201,f779])).

fof(f779,plain,
    ( spl14_142
  <=> v1_funct_2(u1_waybel_0(sK12,sK3(sK12)),u1_struct_0(sK3(sK12)),u1_struct_0(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_142])])).

fof(f390,plain,
    ( v1_funct_2(u1_waybel_0(sK12,sK3(sK12)),u1_struct_0(sK3(sK12)),u1_struct_0(sK12))
    | ~ spl14_18
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f202,f226,f122])).

fof(f762,plain,
    ( ~ spl14_141
    | ~ spl14_130 ),
    inference(avatar_split_clause,[],[f752,f708,f760])).

fof(f752,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1))
    | ~ spl14_130 ),
    inference(unit_resulting_resolution,[],[f709,f749])).

fof(f740,plain,
    ( spl14_138
    | ~ spl14_10
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f391,f218,f172,f738])).

fof(f738,plain,
    ( spl14_138
  <=> v1_funct_2(u1_waybel_0(sK13,sK3(sK13)),u1_struct_0(sK3(sK13)),u1_struct_0(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_138])])).

fof(f391,plain,
    ( v1_funct_2(u1_waybel_0(sK13,sK3(sK13)),u1_struct_0(sK3(sK13)),u1_struct_0(sK13))
    | ~ spl14_10
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f173,f219,f122])).

fof(f733,plain,
    ( spl14_136
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f511,f492,f179,f151,f144,f137,f731])).

fof(f731,plain,
    ( spl14_136
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK10(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_136])])).

fof(f511,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK10(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f493,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',dt_k2_waybel_0)).

fof(f726,plain,
    ( spl14_134
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f510,f484,f179,f151,f144,f137,f724])).

fof(f724,plain,
    ( spl14_134
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_134])])).

fof(f510,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f485,f126])).

fof(f717,plain,
    ( spl14_132
    | ~ spl14_2
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f387,f211,f144,f715])).

fof(f715,plain,
    ( spl14_132
  <=> v1_funct_2(u1_waybel_0(sK0,sK3(sK0)),u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_132])])).

fof(f387,plain,
    ( v1_funct_2(u1_waybel_0(sK0,sK3(sK0)),u1_struct_0(sK3(sK0)),u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f145,f212,f122])).

fof(f710,plain,
    ( spl14_130
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f417,f179,f144,f708])).

fof(f417,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f145,f180,f123])).

fof(f703,plain,
    ( spl14_128
    | ~ spl14_80
    | ~ spl14_114 ),
    inference(avatar_split_clause,[],[f650,f646,f476,f701])).

fof(f701,plain,
    ( spl14_128
  <=> v1_funct_1(u1_waybel_0(sK3(sK3(sK1)),sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_128])])).

fof(f476,plain,
    ( spl14_80
  <=> l1_struct_0(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_80])])).

fof(f646,plain,
    ( spl14_114
  <=> l1_waybel_0(sK3(sK3(sK3(sK1))),sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_114])])).

fof(f650,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK3(sK1)),sK3(sK3(sK3(sK1)))))
    | ~ spl14_80
    | ~ spl14_114 ),
    inference(unit_resulting_resolution,[],[f477,f647,f121])).

fof(f647,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl14_114 ),
    inference(avatar_component_clause,[],[f646])).

fof(f477,plain,
    ( l1_struct_0(sK3(sK3(sK1)))
    | ~ spl14_80 ),
    inference(avatar_component_clause,[],[f476])).

fof(f696,plain,
    ( spl14_126
    | ~ spl14_74
    | ~ spl14_108 ),
    inference(avatar_split_clause,[],[f623,f619,f448,f694])).

fof(f694,plain,
    ( spl14_126
  <=> v1_funct_1(u1_waybel_0(sK3(sK3(sK12)),sK3(sK3(sK3(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_126])])).

fof(f448,plain,
    ( spl14_74
  <=> l1_struct_0(sK3(sK3(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_74])])).

fof(f619,plain,
    ( spl14_108
  <=> l1_waybel_0(sK3(sK3(sK3(sK12))),sK3(sK3(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_108])])).

fof(f623,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK3(sK12)),sK3(sK3(sK3(sK12)))))
    | ~ spl14_74
    | ~ spl14_108 ),
    inference(unit_resulting_resolution,[],[f449,f620,f121])).

fof(f620,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK12))),sK3(sK3(sK12)))
    | ~ spl14_108 ),
    inference(avatar_component_clause,[],[f619])).

fof(f449,plain,
    ( l1_struct_0(sK3(sK3(sK12)))
    | ~ spl14_74 ),
    inference(avatar_component_clause,[],[f448])).

fof(f689,plain,
    ( spl14_124
    | ~ spl14_68
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f596,f583,f414,f687])).

fof(f687,plain,
    ( spl14_124
  <=> v1_funct_1(u1_waybel_0(sK3(sK3(sK13)),sK3(sK3(sK3(sK13))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_124])])).

fof(f414,plain,
    ( spl14_68
  <=> l1_struct_0(sK3(sK3(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f583,plain,
    ( spl14_102
  <=> l1_waybel_0(sK3(sK3(sK3(sK13))),sK3(sK3(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_102])])).

fof(f596,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK3(sK13)),sK3(sK3(sK3(sK13)))))
    | ~ spl14_68
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f415,f584,f121])).

fof(f584,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK13))),sK3(sK3(sK13)))
    | ~ spl14_102 ),
    inference(avatar_component_clause,[],[f583])).

fof(f415,plain,
    ( l1_struct_0(sK3(sK3(sK13)))
    | ~ spl14_68 ),
    inference(avatar_component_clause,[],[f414])).

fof(f682,plain,
    ( spl14_122
    | ~ spl14_62
    | ~ spl14_96 ),
    inference(avatar_split_clause,[],[f551,f547,f382,f680])).

fof(f680,plain,
    ( spl14_122
  <=> v1_funct_1(u1_waybel_0(sK3(sK3(sK0)),sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_122])])).

fof(f382,plain,
    ( spl14_62
  <=> l1_struct_0(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_62])])).

fof(f547,plain,
    ( spl14_96
  <=> l1_waybel_0(sK3(sK3(sK3(sK0))),sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_96])])).

fof(f551,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK3(sK0)),sK3(sK3(sK3(sK0)))))
    | ~ spl14_62
    | ~ spl14_96 ),
    inference(unit_resulting_resolution,[],[f383,f548,f121])).

fof(f548,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl14_96 ),
    inference(avatar_component_clause,[],[f547])).

fof(f383,plain,
    ( l1_struct_0(sK3(sK3(sK0)))
    | ~ spl14_62 ),
    inference(avatar_component_clause,[],[f382])).

fof(f675,plain,
    ( spl14_120
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f509,f179,f151,f144,f137,f673])).

fof(f673,plain,
    ( spl14_120
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK11(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_120])])).

fof(f509,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK11(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f117,f126])).

fof(f667,plain,
    ( spl14_118
    | ~ spl14_116 ),
    inference(avatar_split_clause,[],[f660,f657,f665])).

fof(f657,plain,
    ( spl14_116
  <=> l1_orders_2(sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_116])])).

fof(f660,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK1))))
    | ~ spl14_116 ),
    inference(unit_resulting_resolution,[],[f658,f97])).

fof(f658,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK1))))
    | ~ spl14_116 ),
    inference(avatar_component_clause,[],[f657])).

fof(f659,plain,
    ( spl14_116
    | ~ spl14_80
    | ~ spl14_114 ),
    inference(avatar_split_clause,[],[f649,f646,f476,f657])).

fof(f649,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK1))))
    | ~ spl14_80
    | ~ spl14_114 ),
    inference(unit_resulting_resolution,[],[f477,f647,f99])).

fof(f648,plain,
    ( spl14_114
    | ~ spl14_80 ),
    inference(avatar_split_clause,[],[f479,f476,f646])).

fof(f479,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK1))),sK3(sK3(sK1)))
    | ~ spl14_80 ),
    inference(unit_resulting_resolution,[],[f477,f100])).

fof(f640,plain,
    ( spl14_112
    | ~ spl14_110 ),
    inference(avatar_split_clause,[],[f633,f630,f638])).

fof(f630,plain,
    ( spl14_110
  <=> l1_orders_2(sK3(sK3(sK3(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_110])])).

fof(f633,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK12))))
    | ~ spl14_110 ),
    inference(unit_resulting_resolution,[],[f631,f97])).

fof(f631,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK12))))
    | ~ spl14_110 ),
    inference(avatar_component_clause,[],[f630])).

fof(f632,plain,
    ( spl14_110
    | ~ spl14_74
    | ~ spl14_108 ),
    inference(avatar_split_clause,[],[f622,f619,f448,f630])).

fof(f622,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK12))))
    | ~ spl14_74
    | ~ spl14_108 ),
    inference(unit_resulting_resolution,[],[f449,f620,f99])).

fof(f621,plain,
    ( spl14_108
    | ~ spl14_74 ),
    inference(avatar_split_clause,[],[f451,f448,f619])).

fof(f451,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK12))),sK3(sK3(sK12)))
    | ~ spl14_74 ),
    inference(unit_resulting_resolution,[],[f449,f100])).

fof(f613,plain,
    ( spl14_106
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f606,f603,f611])).

fof(f603,plain,
    ( spl14_104
  <=> l1_orders_2(sK3(sK3(sK3(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_104])])).

fof(f606,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK13))))
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f604,f97])).

fof(f604,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK13))))
    | ~ spl14_104 ),
    inference(avatar_component_clause,[],[f603])).

fof(f605,plain,
    ( spl14_104
    | ~ spl14_68
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f595,f583,f414,f603])).

fof(f595,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK13))))
    | ~ spl14_68
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f415,f584,f99])).

fof(f585,plain,
    ( spl14_102
    | ~ spl14_68 ),
    inference(avatar_split_clause,[],[f424,f414,f583])).

fof(f424,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK13))),sK3(sK3(sK13)))
    | ~ spl14_68 ),
    inference(unit_resulting_resolution,[],[f415,f100])).

fof(f577,plain,
    ( spl14_100
    | ~ spl14_98 ),
    inference(avatar_split_clause,[],[f570,f567,f575])).

fof(f567,plain,
    ( spl14_98
  <=> l1_orders_2(sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_98])])).

fof(f570,plain,
    ( l1_struct_0(sK3(sK3(sK3(sK0))))
    | ~ spl14_98 ),
    inference(unit_resulting_resolution,[],[f568,f97])).

fof(f568,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK0))))
    | ~ spl14_98 ),
    inference(avatar_component_clause,[],[f567])).

fof(f569,plain,
    ( spl14_98
    | ~ spl14_62
    | ~ spl14_96 ),
    inference(avatar_split_clause,[],[f550,f547,f382,f567])).

fof(f550,plain,
    ( l1_orders_2(sK3(sK3(sK3(sK0))))
    | ~ spl14_62
    | ~ spl14_96 ),
    inference(unit_resulting_resolution,[],[f383,f548,f99])).

fof(f549,plain,
    ( spl14_96
    | ~ spl14_62 ),
    inference(avatar_split_clause,[],[f385,f382,f547])).

fof(f385,plain,
    ( l1_waybel_0(sK3(sK3(sK3(sK0))),sK3(sK3(sK0)))
    | ~ spl14_62 ),
    inference(unit_resulting_resolution,[],[f383,f100])).

fof(f541,plain,
    ( spl14_94
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f386,f179,f144,f539])).

fof(f539,plain,
    ( spl14_94
  <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_94])])).

fof(f386,plain,
    ( v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f145,f180,f122])).

fof(f525,plain,
    ( spl14_92
    | ~ spl14_48
    | ~ spl14_76 ),
    inference(avatar_split_clause,[],[f461,f456,f329,f523])).

fof(f523,plain,
    ( spl14_92
  <=> v1_funct_1(u1_waybel_0(sK3(sK1),sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_92])])).

fof(f329,plain,
    ( spl14_48
  <=> l1_struct_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).

fof(f456,plain,
    ( spl14_76
  <=> l1_waybel_0(sK3(sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_76])])).

fof(f461,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK1),sK3(sK3(sK1))))
    | ~ spl14_48
    | ~ spl14_76 ),
    inference(unit_resulting_resolution,[],[f330,f457,f121])).

fof(f457,plain,
    ( l1_waybel_0(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl14_76 ),
    inference(avatar_component_clause,[],[f456])).

fof(f330,plain,
    ( l1_struct_0(sK3(sK1))
    | ~ spl14_48 ),
    inference(avatar_component_clause,[],[f329])).

fof(f518,plain,
    ( spl14_90
    | ~ spl14_40
    | ~ spl14_70 ),
    inference(avatar_split_clause,[],[f434,f429,f297,f516])).

fof(f516,plain,
    ( spl14_90
  <=> v1_funct_1(u1_waybel_0(sK3(sK12),sK3(sK3(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_90])])).

fof(f297,plain,
    ( spl14_40
  <=> l1_struct_0(sK3(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f429,plain,
    ( spl14_70
  <=> l1_waybel_0(sK3(sK3(sK12)),sK3(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_70])])).

fof(f434,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK12),sK3(sK3(sK12))))
    | ~ spl14_40
    | ~ spl14_70 ),
    inference(unit_resulting_resolution,[],[f298,f430,f121])).

fof(f430,plain,
    ( l1_waybel_0(sK3(sK3(sK12)),sK3(sK12))
    | ~ spl14_70 ),
    inference(avatar_component_clause,[],[f429])).

fof(f298,plain,
    ( l1_struct_0(sK3(sK12))
    | ~ spl14_40 ),
    inference(avatar_component_clause,[],[f297])).

fof(f508,plain,
    ( spl14_88
    | ~ spl14_38
    | ~ spl14_64 ),
    inference(avatar_split_clause,[],[f400,f396,f284,f506])).

fof(f506,plain,
    ( spl14_88
  <=> v1_funct_1(u1_waybel_0(sK3(sK13),sK3(sK3(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_88])])).

fof(f284,plain,
    ( spl14_38
  <=> l1_struct_0(sK3(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).

fof(f396,plain,
    ( spl14_64
  <=> l1_waybel_0(sK3(sK3(sK13)),sK3(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_64])])).

fof(f400,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK13),sK3(sK3(sK13))))
    | ~ spl14_38
    | ~ spl14_64 ),
    inference(unit_resulting_resolution,[],[f285,f397,f121])).

fof(f397,plain,
    ( l1_waybel_0(sK3(sK3(sK13)),sK3(sK13))
    | ~ spl14_64 ),
    inference(avatar_component_clause,[],[f396])).

fof(f285,plain,
    ( l1_struct_0(sK3(sK13))
    | ~ spl14_38 ),
    inference(avatar_component_clause,[],[f284])).

fof(f501,plain,
    ( spl14_86
    | ~ spl14_34
    | ~ spl14_58 ),
    inference(avatar_split_clause,[],[f368,f365,f269,f499])).

fof(f499,plain,
    ( spl14_86
  <=> v1_funct_1(u1_waybel_0(sK3(sK0),sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_86])])).

fof(f269,plain,
    ( spl14_34
  <=> l1_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f365,plain,
    ( spl14_58
  <=> l1_waybel_0(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_58])])).

fof(f368,plain,
    ( v1_funct_1(u1_waybel_0(sK3(sK0),sK3(sK3(sK0))))
    | ~ spl14_34
    | ~ spl14_58 ),
    inference(unit_resulting_resolution,[],[f270,f366,f121])).

fof(f366,plain,
    ( l1_waybel_0(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl14_58 ),
    inference(avatar_component_clause,[],[f365])).

fof(f270,plain,
    ( l1_struct_0(sK3(sK0))
    | ~ spl14_34 ),
    inference(avatar_component_clause,[],[f269])).

fof(f494,plain,
    ( spl14_84
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f487,f186,f179,f151,f144,f137,f492])).

fof(f487,plain,
    ( m1_subset_1(sK10(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f187,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f486,plain,
    ( spl14_82
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | spl14_17 ),
    inference(avatar_split_clause,[],[f470,f193,f179,f151,f144,f137,f484])).

fof(f470,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_17 ),
    inference(unit_resulting_resolution,[],[f138,f145,f152,f180,f194,f110])).

fof(f478,plain,
    ( spl14_80
    | ~ spl14_78 ),
    inference(avatar_split_clause,[],[f471,f467,f476])).

fof(f467,plain,
    ( spl14_78
  <=> l1_orders_2(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_78])])).

fof(f471,plain,
    ( l1_struct_0(sK3(sK3(sK1)))
    | ~ spl14_78 ),
    inference(unit_resulting_resolution,[],[f468,f97])).

fof(f468,plain,
    ( l1_orders_2(sK3(sK3(sK1)))
    | ~ spl14_78 ),
    inference(avatar_component_clause,[],[f467])).

fof(f469,plain,
    ( spl14_78
    | ~ spl14_48
    | ~ spl14_76 ),
    inference(avatar_split_clause,[],[f462,f456,f329,f467])).

fof(f462,plain,
    ( l1_orders_2(sK3(sK3(sK1)))
    | ~ spl14_48
    | ~ spl14_76 ),
    inference(unit_resulting_resolution,[],[f330,f457,f99])).

fof(f458,plain,
    ( spl14_76
    | ~ spl14_48 ),
    inference(avatar_split_clause,[],[f332,f329,f456])).

fof(f332,plain,
    ( l1_waybel_0(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl14_48 ),
    inference(unit_resulting_resolution,[],[f330,f100])).

fof(f450,plain,
    ( spl14_74
    | ~ spl14_72 ),
    inference(avatar_split_clause,[],[f443,f440,f448])).

fof(f440,plain,
    ( spl14_72
  <=> l1_orders_2(sK3(sK3(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_72])])).

fof(f443,plain,
    ( l1_struct_0(sK3(sK3(sK12)))
    | ~ spl14_72 ),
    inference(unit_resulting_resolution,[],[f441,f97])).

fof(f441,plain,
    ( l1_orders_2(sK3(sK3(sK12)))
    | ~ spl14_72 ),
    inference(avatar_component_clause,[],[f440])).

fof(f442,plain,
    ( spl14_72
    | ~ spl14_40
    | ~ spl14_70 ),
    inference(avatar_split_clause,[],[f435,f429,f297,f440])).

fof(f435,plain,
    ( l1_orders_2(sK3(sK3(sK12)))
    | ~ spl14_40
    | ~ spl14_70 ),
    inference(unit_resulting_resolution,[],[f298,f430,f99])).

fof(f431,plain,
    ( spl14_70
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f300,f297,f429])).

fof(f300,plain,
    ( l1_waybel_0(sK3(sK3(sK12)),sK3(sK12))
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f298,f100])).

fof(f416,plain,
    ( spl14_68
    | ~ spl14_66 ),
    inference(avatar_split_clause,[],[f409,f406,f414])).

fof(f406,plain,
    ( spl14_66
  <=> l1_orders_2(sK3(sK3(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_66])])).

fof(f409,plain,
    ( l1_struct_0(sK3(sK3(sK13)))
    | ~ spl14_66 ),
    inference(unit_resulting_resolution,[],[f407,f97])).

fof(f407,plain,
    ( l1_orders_2(sK3(sK3(sK13)))
    | ~ spl14_66 ),
    inference(avatar_component_clause,[],[f406])).

fof(f408,plain,
    ( spl14_66
    | ~ spl14_38
    | ~ spl14_64 ),
    inference(avatar_split_clause,[],[f401,f396,f284,f406])).

fof(f401,plain,
    ( l1_orders_2(sK3(sK3(sK13)))
    | ~ spl14_38
    | ~ spl14_64 ),
    inference(unit_resulting_resolution,[],[f285,f397,f99])).

fof(f398,plain,
    ( spl14_64
    | ~ spl14_38 ),
    inference(avatar_split_clause,[],[f292,f284,f396])).

fof(f292,plain,
    ( l1_waybel_0(sK3(sK3(sK13)),sK3(sK13))
    | ~ spl14_38 ),
    inference(unit_resulting_resolution,[],[f285,f100])).

fof(f384,plain,
    ( spl14_62
    | ~ spl14_60 ),
    inference(avatar_split_clause,[],[f377,f374,f382])).

fof(f374,plain,
    ( spl14_60
  <=> l1_orders_2(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_60])])).

fof(f377,plain,
    ( l1_struct_0(sK3(sK3(sK0)))
    | ~ spl14_60 ),
    inference(unit_resulting_resolution,[],[f375,f97])).

fof(f375,plain,
    ( l1_orders_2(sK3(sK3(sK0)))
    | ~ spl14_60 ),
    inference(avatar_component_clause,[],[f374])).

fof(f376,plain,
    ( spl14_60
    | ~ spl14_34
    | ~ spl14_58 ),
    inference(avatar_split_clause,[],[f369,f365,f269,f374])).

fof(f369,plain,
    ( l1_orders_2(sK3(sK3(sK0)))
    | ~ spl14_34
    | ~ spl14_58 ),
    inference(unit_resulting_resolution,[],[f270,f366,f99])).

fof(f367,plain,
    ( spl14_58
    | ~ spl14_34 ),
    inference(avatar_split_clause,[],[f272,f269,f365])).

fof(f272,plain,
    ( l1_waybel_0(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl14_34 ),
    inference(unit_resulting_resolution,[],[f270,f100])).

fof(f360,plain,
    ( spl14_56
    | ~ spl14_28
    | ~ spl14_44 ),
    inference(avatar_split_clause,[],[f315,f312,f244,f358])).

fof(f358,plain,
    ( spl14_56
  <=> v1_funct_1(u1_waybel_0(sK1,sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_56])])).

fof(f315,plain,
    ( v1_funct_1(u1_waybel_0(sK1,sK3(sK1)))
    | ~ spl14_28
    | ~ spl14_44 ),
    inference(unit_resulting_resolution,[],[f245,f313,f121])).

fof(f353,plain,
    ( spl14_54
    | ~ spl14_18
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f291,f225,f201,f351])).

fof(f351,plain,
    ( spl14_54
  <=> v1_funct_1(u1_waybel_0(sK12,sK3(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_54])])).

fof(f291,plain,
    ( v1_funct_1(u1_waybel_0(sK12,sK3(sK12)))
    | ~ spl14_18
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f202,f226,f121])).

fof(f346,plain,
    ( spl14_52
    | ~ spl14_10
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f290,f218,f172,f344])).

fof(f344,plain,
    ( spl14_52
  <=> v1_funct_1(u1_waybel_0(sK13,sK3(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_52])])).

fof(f290,plain,
    ( v1_funct_1(u1_waybel_0(sK13,sK3(sK13)))
    | ~ spl14_10
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f173,f219,f121])).

fof(f339,plain,
    ( spl14_50
    | ~ spl14_2
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f289,f211,f144,f337])).

fof(f337,plain,
    ( spl14_50
  <=> v1_funct_1(u1_waybel_0(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_50])])).

fof(f289,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK3(sK0)))
    | ~ spl14_2
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f145,f212,f121])).

fof(f331,plain,
    ( spl14_48
    | ~ spl14_46 ),
    inference(avatar_split_clause,[],[f324,f321,f329])).

fof(f321,plain,
    ( spl14_46
  <=> l1_orders_2(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_46])])).

fof(f324,plain,
    ( l1_struct_0(sK3(sK1))
    | ~ spl14_46 ),
    inference(unit_resulting_resolution,[],[f322,f97])).

fof(f322,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl14_46 ),
    inference(avatar_component_clause,[],[f321])).

fof(f323,plain,
    ( spl14_46
    | ~ spl14_28
    | ~ spl14_44 ),
    inference(avatar_split_clause,[],[f316,f312,f244,f321])).

fof(f316,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl14_28
    | ~ spl14_44 ),
    inference(unit_resulting_resolution,[],[f245,f313,f99])).

fof(f314,plain,
    ( spl14_44
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f247,f244,f312])).

fof(f247,plain,
    ( l1_waybel_0(sK3(sK1),sK1)
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f245,f100])).

fof(f307,plain,
    ( spl14_42
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f288,f179,f144,f305])).

fof(f288,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f145,f180,f121])).

fof(f299,plain,
    ( spl14_40
    | ~ spl14_36 ),
    inference(avatar_split_clause,[],[f287,f277,f297])).

fof(f277,plain,
    ( spl14_36
  <=> l1_orders_2(sK3(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).

fof(f287,plain,
    ( l1_struct_0(sK3(sK12))
    | ~ spl14_36 ),
    inference(unit_resulting_resolution,[],[f278,f97])).

fof(f278,plain,
    ( l1_orders_2(sK3(sK12))
    | ~ spl14_36 ),
    inference(avatar_component_clause,[],[f277])).

fof(f286,plain,
    ( spl14_38
    | ~ spl14_32 ),
    inference(avatar_split_clause,[],[f263,f260,f284])).

fof(f260,plain,
    ( spl14_32
  <=> l1_orders_2(sK3(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f263,plain,
    ( l1_struct_0(sK3(sK13))
    | ~ spl14_32 ),
    inference(unit_resulting_resolution,[],[f261,f97])).

fof(f261,plain,
    ( l1_orders_2(sK3(sK13))
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f260])).

fof(f279,plain,
    ( spl14_36
    | ~ spl14_18
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f231,f225,f201,f277])).

fof(f231,plain,
    ( l1_orders_2(sK3(sK12))
    | ~ spl14_18
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f202,f226,f99])).

fof(f271,plain,
    ( spl14_34
    | ~ spl14_30 ),
    inference(avatar_split_clause,[],[f255,f252,f269])).

fof(f252,plain,
    ( spl14_30
  <=> l1_orders_2(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f255,plain,
    ( l1_struct_0(sK3(sK0))
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f253,f97])).

fof(f253,plain,
    ( l1_orders_2(sK3(sK0))
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f252])).

fof(f262,plain,
    ( spl14_32
    | ~ spl14_10
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f230,f218,f172,f260])).

fof(f230,plain,
    ( l1_orders_2(sK3(sK13))
    | ~ spl14_10
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f173,f219,f99])).

fof(f254,plain,
    ( spl14_30
    | ~ spl14_2
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f229,f211,f144,f252])).

fof(f229,plain,
    ( l1_orders_2(sK3(sK0))
    | ~ spl14_2
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f145,f212,f99])).

fof(f246,plain,
    ( spl14_28
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f239,f236,f244])).

fof(f239,plain,
    ( l1_struct_0(sK1)
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f237,f97])).

fof(f238,plain,
    ( spl14_26
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f228,f179,f144,f236])).

fof(f228,plain,
    ( l1_orders_2(sK1)
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f145,f180,f99])).

fof(f227,plain,
    ( spl14_24
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f206,f201,f225])).

fof(f206,plain,
    ( l1_waybel_0(sK3(sK12),sK12)
    | ~ spl14_18 ),
    inference(unit_resulting_resolution,[],[f202,f100])).

fof(f220,plain,
    ( spl14_22
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f205,f172,f218])).

fof(f205,plain,
    ( l1_waybel_0(sK3(sK13),sK13)
    | ~ spl14_10 ),
    inference(unit_resulting_resolution,[],[f173,f100])).

fof(f213,plain,
    ( spl14_20
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f204,f144,f211])).

fof(f204,plain,
    ( l1_waybel_0(sK3(sK0),sK0)
    | ~ spl14_2 ),
    inference(unit_resulting_resolution,[],[f145,f100])).

fof(f203,plain,
    ( spl14_18
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f196,f165,f201])).

fof(f165,plain,
    ( spl14_8
  <=> l1_orders_2(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f196,plain,
    ( l1_struct_0(sK12)
    | ~ spl14_8 ),
    inference(unit_resulting_resolution,[],[f166,f97])).

fof(f166,plain,
    ( l1_orders_2(sK12)
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f195,plain,(
    ~ spl14_17 ),
    inference(avatar_split_clause,[],[f96,f193])).

fof(f96,plain,(
    ~ r2_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK2)
    & r1_waybel_0(sK0,sK1,sK2)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_waybel_0(X0,X1,X2)
                & r1_waybel_0(X0,X1,X2) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(sK0,X1,X2)
              & r1_waybel_0(sK0,X1,X2) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_waybel_0(X0,sK1,X2)
            & r1_waybel_0(X0,sK1,X2) )
        & l1_waybel_0(sK1,X0)
        & v7_waybel_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_waybel_0(X0,X1,X2)
          & r1_waybel_0(X0,X1,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK2)
        & r1_waybel_0(X0,X1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
               => r2_waybel_0(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
               => r2_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',t28_yellow_6)).

fof(f188,plain,(
    spl14_14 ),
    inference(avatar_split_clause,[],[f95,f186])).

fof(f95,plain,(
    r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f181,plain,(
    spl14_12 ),
    inference(avatar_split_clause,[],[f94,f179])).

fof(f94,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f174,plain,(
    spl14_10 ),
    inference(avatar_split_clause,[],[f132,f172])).

fof(f132,plain,(
    l1_struct_0(sK13) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    l1_struct_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f20,f88])).

fof(f88,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK13) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',existence_l1_struct_0)).

fof(f167,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f131,f165])).

fof(f131,plain,(
    l1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    l1_orders_2(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f19,f86])).

fof(f86,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK12) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t28_yellow_6.p',existence_l1_orders_2)).

fof(f160,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f93,f158])).

fof(f93,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f153,plain,(
    ~ spl14_5 ),
    inference(avatar_split_clause,[],[f92,f151])).

fof(f92,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f146,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f91,f144])).

fof(f91,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f139,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f90,f137])).

fof(f90,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
