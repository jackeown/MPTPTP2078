%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1210+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:12 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 204 expanded)
%              Number of leaves         :   24 (  99 expanded)
%              Depth                    :    7
%              Number of atoms          :  374 ( 816 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2345,f2350,f2355,f2360,f2365,f2370,f2387,f2447,f2459,f2465,f2480,f2587,f2765,f2789,f3134,f3150])).

fof(f3150,plain,
    ( ~ spl32_21
    | ~ spl32_2
    | ~ spl32_78
    | spl32_1
    | ~ spl32_62 ),
    inference(avatar_split_clause,[],[f3149,f2787,f2342,f3131,f2347,f2477])).

fof(f2477,plain,
    ( spl32_21
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_21])])).

fof(f2347,plain,
    ( spl32_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_2])])).

fof(f3131,plain,
    ( spl32_78
  <=> r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_78])])).

fof(f2342,plain,
    ( spl32_1
  <=> r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_1])])).

fof(f2787,plain,
    ( spl32_62
  <=> ! [X1,X0] :
        ( ~ r1_lattices(sK0,X0,X1)
        | r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_62])])).

fof(f3149,plain,
    ( ~ r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | spl32_1
    | ~ spl32_62 ),
    inference(resolution,[],[f2788,f2344])).

fof(f2344,plain,
    ( ~ r3_lattices(sK0,sK1,k6_lattices(sK0))
    | spl32_1 ),
    inference(avatar_component_clause,[],[f2342])).

fof(f2788,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl32_62 ),
    inference(avatar_component_clause,[],[f2787])).

fof(f3134,plain,
    ( ~ spl32_21
    | ~ spl32_2
    | spl32_78
    | ~ spl32_31
    | ~ spl32_59 ),
    inference(avatar_split_clause,[],[f3122,f2763,f2584,f3131,f2347,f2477])).

fof(f2584,plain,
    ( spl32_31
  <=> sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_31])])).

fof(f2763,plain,
    ( spl32_59
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X1,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_59])])).

fof(f3122,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl32_31
    | ~ spl32_59 ),
    inference(superposition,[],[f2764,f2586])).

fof(f2586,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl32_31 ),
    inference(avatar_component_clause,[],[f2584])).

fof(f2764,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k4_lattices(sK0,X1,X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl32_59 ),
    inference(avatar_component_clause,[],[f2763])).

fof(f2789,plain,
    ( ~ spl32_16
    | ~ spl32_18
    | ~ spl32_19
    | ~ spl32_3
    | spl32_62
    | spl32_6 ),
    inference(avatar_split_clause,[],[f2785,f2367,f2787,f2352,f2462,f2456,f2444])).

fof(f2444,plain,
    ( spl32_16
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_16])])).

fof(f2456,plain,
    ( spl32_18
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_18])])).

fof(f2462,plain,
    ( spl32_19
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_19])])).

fof(f2352,plain,
    ( spl32_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_3])])).

fof(f2367,plain,
    ( spl32_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_6])])).

fof(f2785,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v6_lattices(sK0)
        | r3_lattices(sK0,X0,X1) )
    | spl32_6 ),
    inference(resolution,[],[f2221,f2369])).

fof(f2369,plain,
    ( ~ v2_struct_0(sK0)
    | spl32_6 ),
    inference(avatar_component_clause,[],[f2367])).

fof(f2221,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2159])).

fof(f2159,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2076])).

fof(f2076,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2075])).

fof(f2075,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2042])).

fof(f2042,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f2765,plain,
    ( ~ spl32_16
    | ~ spl32_18
    | ~ spl32_3
    | spl32_59
    | spl32_6 ),
    inference(avatar_split_clause,[],[f2739,f2367,f2763,f2352,f2456,f2444])).

fof(f2739,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v6_lattices(sK0)
        | r1_lattices(sK0,k4_lattices(sK0,X1,X0),X1) )
    | spl32_6 ),
    inference(resolution,[],[f2302,f2369])).

fof(f2302,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f2136])).

fof(f2136,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2135])).

fof(f2135,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2049])).

fof(f2049,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(f2587,plain,
    ( spl32_31
    | ~ spl32_2
    | ~ spl32_3
    | ~ spl32_4
    | ~ spl32_5
    | spl32_6 ),
    inference(avatar_split_clause,[],[f2576,f2367,f2362,f2357,f2352,f2347,f2584])).

fof(f2357,plain,
    ( spl32_4
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_4])])).

fof(f2362,plain,
    ( spl32_5
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_5])])).

fof(f2576,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl32_2
    | ~ spl32_3
    | ~ spl32_4
    | ~ spl32_5
    | spl32_6 ),
    inference(unit_resulting_resolution,[],[f2369,f2364,f2359,f2354,f2349,f2229])).

fof(f2229,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2086])).

fof(f2086,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2085])).

fof(f2085,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2060])).

fof(f2060,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f2349,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl32_2 ),
    inference(avatar_component_clause,[],[f2347])).

fof(f2354,plain,
    ( l3_lattices(sK0)
    | ~ spl32_3 ),
    inference(avatar_component_clause,[],[f2352])).

fof(f2359,plain,
    ( v14_lattices(sK0)
    | ~ spl32_4 ),
    inference(avatar_component_clause,[],[f2357])).

fof(f2364,plain,
    ( v10_lattices(sK0)
    | ~ spl32_5 ),
    inference(avatar_component_clause,[],[f2362])).

fof(f2480,plain,
    ( spl32_21
    | spl32_6
    | ~ spl32_9 ),
    inference(avatar_split_clause,[],[f2475,f2384,f2367,f2477])).

fof(f2384,plain,
    ( spl32_9
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_9])])).

fof(f2475,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | spl32_6
    | ~ spl32_9 ),
    inference(unit_resulting_resolution,[],[f2369,f2386,f2227])).

fof(f2227,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2082])).

fof(f2082,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2081])).

fof(f2081,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2030])).

fof(f2030,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f2386,plain,
    ( l2_lattices(sK0)
    | ~ spl32_9 ),
    inference(avatar_component_clause,[],[f2384])).

fof(f2465,plain,
    ( spl32_19
    | ~ spl32_3
    | ~ spl32_5
    | spl32_6 ),
    inference(avatar_split_clause,[],[f2460,f2367,f2362,f2352,f2462])).

fof(f2460,plain,
    ( v9_lattices(sK0)
    | ~ spl32_3
    | ~ spl32_5
    | spl32_6 ),
    inference(unit_resulting_resolution,[],[f2354,f2369,f2364,f2321])).

fof(f2321,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2153,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f2152])).

fof(f2152,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2009])).

fof(f2009,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f2459,plain,
    ( spl32_18
    | ~ spl32_3
    | ~ spl32_5
    | spl32_6 ),
    inference(avatar_split_clause,[],[f2454,f2367,f2362,f2352,f2456])).

fof(f2454,plain,
    ( v8_lattices(sK0)
    | ~ spl32_3
    | ~ spl32_5
    | spl32_6 ),
    inference(unit_resulting_resolution,[],[f2354,f2369,f2364,f2320])).

fof(f2320,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2447,plain,
    ( spl32_16
    | ~ spl32_3
    | ~ spl32_5
    | spl32_6 ),
    inference(avatar_split_clause,[],[f2442,f2367,f2362,f2352,f2444])).

fof(f2442,plain,
    ( v6_lattices(sK0)
    | ~ spl32_3
    | ~ spl32_5
    | spl32_6 ),
    inference(unit_resulting_resolution,[],[f2354,f2369,f2364,f2318])).

fof(f2318,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2387,plain,
    ( spl32_9
    | ~ spl32_3 ),
    inference(avatar_split_clause,[],[f2376,f2352,f2384])).

fof(f2376,plain,
    ( l2_lattices(sK0)
    | ~ spl32_3 ),
    inference(unit_resulting_resolution,[],[f2354,f2307])).

fof(f2307,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2143,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2068])).

fof(f2068,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2033])).

fof(f2033,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f2370,plain,(
    ~ spl32_6 ),
    inference(avatar_split_clause,[],[f2214,f2367])).

fof(f2214,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2158])).

fof(f2158,plain,
    ( ~ r3_lattices(sK0,sK1,k6_lattices(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2074,f2157,f2156])).

fof(f2156,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_lattices(X0,X1,k6_lattices(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r3_lattices(sK0,X1,k6_lattices(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2157,plain,
    ( ? [X1] :
        ( ~ r3_lattices(sK0,X1,k6_lattices(sK0))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ r3_lattices(sK0,sK1,k6_lattices(sK0))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2074,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2073])).

fof(f2073,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,X1,k6_lattices(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2063])).

fof(f2063,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,X1,k6_lattices(X0)) ) ) ),
    inference(negated_conjecture,[],[f2062])).

fof(f2062,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,X1,k6_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattices)).

fof(f2365,plain,(
    spl32_5 ),
    inference(avatar_split_clause,[],[f2215,f2362])).

fof(f2215,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2158])).

fof(f2360,plain,(
    spl32_4 ),
    inference(avatar_split_clause,[],[f2216,f2357])).

fof(f2216,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f2158])).

fof(f2355,plain,(
    spl32_3 ),
    inference(avatar_split_clause,[],[f2217,f2352])).

fof(f2217,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2158])).

fof(f2350,plain,(
    spl32_2 ),
    inference(avatar_split_clause,[],[f2218,f2347])).

fof(f2218,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2158])).

fof(f2345,plain,(
    ~ spl32_1 ),
    inference(avatar_split_clause,[],[f2219,f2342])).

fof(f2219,plain,(
    ~ r3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(cnf_transformation,[],[f2158])).
%------------------------------------------------------------------------------
