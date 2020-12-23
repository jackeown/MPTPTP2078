%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t17_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:37 EDT 2019

% Result     : Theorem 28.97s
% Output     : Refutation 28.97s
% Verified   : 
% Statistics : Number of formulae       : 1300 (33613 expanded)
%              Number of leaves         :  300 (11474 expanded)
%              Depth                    :   24
%              Number of atoms          : 6939 (204759 expanded)
%              Number of equality atoms :   20 (7718 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4662,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f154,f161,f168,f175,f182,f189,f198,f205,f222,f244,f260,f269,f304,f331,f338,f345,f355,f362,f369,f385,f386,f438,f454,f505,f506,f507,f508,f523,f530,f542,f543,f550,f551,f557,f558,f582,f758,f768,f784,f832,f839,f849,f950,f957,f964,f971,f978,f985,f992,f1003,f1004,f1005,f1006,f1007,f1152,f1159,f1166,f1173,f1180,f1187,f1194,f1198,f1202,f1242,f1355,f1378,f1394,f1401,f1408,f1415,f1422,f1429,f1437,f1448,f1456,f1483,f1490,f1497,f1504,f1511,f1518,f1519,f1526,f1527,f1534,f1535,f1536,f1543,f1544,f1591,f1598,f1602,f1645,f1652,f1659,f1666,f1673,f1680,f1687,f1701,f1739,f1746,f1753,f1806,f1813,f1820,f1824,f1840,f1841,f1842,f1843,f1844,f1845,f1947,f2054,f2061,f2062,f2063,f2070,f2071,f2102,f2143,f2174,f2181,f2182,f2189,f2190,f2197,f2213,f2220,f2221,f2228,f2229,f2236,f2250,f2257,f2264,f2271,f2278,f2285,f2292,f2306,f2313,f2320,f2327,f2334,f2341,f2348,f2364,f2372,f2396,f2403,f2434,f2441,f2448,f2455,f2462,f2469,f2476,f2483,f2487,f2491,f2517,f2524,f2531,f2538,f2545,f2552,f2559,f2560,f2567,f2568,f2569,f2576,f2577,f2586,f2601,f2644,f2651,f2658,f2665,f2672,f2673,f2680,f2687,f2694,f2701,f2702,f2709,f2716,f2723,f2730,f2737,f2738,f2745,f2746,f2747,f2748,f2755,f2756,f2766,f2782,f2789,f2796,f2803,f2810,f2817,f2824,f2843,f2850,f2857,f2858,f2865,f2879,f2886,f2887,f2894,f2895,f2902,f2923,f2930,f2937,f2938,f2945,f2949,f2966,f2973,f2980,f3002,f3020,f3021,f3022,f3023,f3024,f3040,f3047,f3054,f3070,f3074,f3094,f3159,f3173,f3196,f3300,f3307,f3314,f3321,f3422,f3459,f3472,f3503,f3587,f3588,f3592,f3654,f3658,f3662,f3681,f3682,f4131,f4258,f4265,f4272,f4279,f4286,f4293,f4300,f4307,f4314,f4321,f4331,f4335,f4343,f4357,f4364,f4382,f4383,f4384,f4385,f4386,f4396,f4406,f4425,f4432,f4433,f4441,f4457,f4464,f4465,f4472,f4473,f4480,f4527,f4534,f4541,f4548,f4555,f4562,f4563,f4564,f4565,f4566,f4573,f4580,f4581,f4588,f4589,f4596,f4597,f4598,f4605,f4606,f4613,f4614,f4615,f4616,f4617,f4618,f4619,f4620,f4621,f4622,f4629,f4630,f4638,f4647,f4654,f4661])).

fof(f4661,plain,
    ( spl16_506
    | ~ spl16_224 ),
    inference(avatar_split_clause,[],[f4641,f2283,f4659])).

fof(f4659,plain,
    ( spl16_506
  <=> m1_subset_1(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_506])])).

fof(f2283,plain,
    ( spl16_224
  <=> r2_hidden(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_224])])).

fof(f4641,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_224 ),
    inference(unit_resulting_resolution,[],[f2284,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t1_subset)).

fof(f2284,plain,
    ( r2_hidden(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_224 ),
    inference(avatar_component_clause,[],[f2283])).

fof(f4654,plain,
    ( ~ spl16_505
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_224 ),
    inference(avatar_split_clause,[],[f4642,f2283,f173,f166,f159,f152,f145,f4652])).

fof(f4652,plain,
    ( spl16_505
  <=> ~ r2_hidden(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_505])])).

fof(f145,plain,
    ( spl16_3
  <=> ~ r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f152,plain,
    ( spl16_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f159,plain,
    ( spl16_6
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f166,plain,
    ( spl16_8
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f173,plain,
    ( spl16_11
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f4642,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_224 ),
    inference(unit_resulting_resolution,[],[f174,f160,f167,f153,f146,f2284,f1759])).

fof(f1759,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,X2)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,X2)
      | ~ v3_lattice3(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f1757])).

fof(f1757,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,X2)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ v3_lattice3(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f1123,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( sK13(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
          | ! [X3] :
              ( ~ r1_lattice3(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r1_lattice3(X1,X2,sK13(X0,X1,X2))
            & sK13(X0,X1,X2) = X0
            & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f80,f81])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_lattice3(X1,X2,X4)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r1_lattice3(X1,X2,sK13(X0,X1,X2))
        & sK13(X0,X1,X2) = X0
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
          | ! [X3] :
              ( ~ r1_lattice3(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r1_lattice3(X1,X2,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
          | ! [X3] :
              ( ~ r1_lattice3(X1,X2,X3)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r1_lattice3(X1,X2,X3)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_orders_2(X1)
        & v3_lattice3(X1)
        & v5_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',fraenkel_a_2_0_yellow_0)).

fof(f1123,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK13(X1,X0,X2),X2)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,a_2_0_yellow_0(X0,X2))
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f1119])).

fof(f1119,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(sK13(X1,X0,X2),X2)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,a_2_0_yellow_0(X0,X2))
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,a_2_0_yellow_0(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f725,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f725,plain,(
    ! [X21,X19,X20] :
      ( ~ m1_subset_1(sK13(X20,X19,X21),u1_struct_0(X19))
      | ~ v5_orders_2(X19)
      | ~ r2_hidden(sK13(X20,X19,X21),X21)
      | r2_yellow_0(X19,X21)
      | ~ l1_orders_2(X19)
      | ~ r2_hidden(X20,a_2_0_yellow_0(X19,X21))
      | ~ v3_lattice3(X19)
      | v2_struct_0(X19) ) ),
    inference(duplicate_literal_removal,[],[f724])).

fof(f724,plain,(
    ! [X21,X19,X20] :
      ( ~ l1_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ r2_hidden(sK13(X20,X19,X21),X21)
      | r2_yellow_0(X19,X21)
      | ~ m1_subset_1(sK13(X20,X19,X21),u1_struct_0(X19))
      | ~ r2_hidden(X20,a_2_0_yellow_0(X19,X21))
      | ~ l1_orders_2(X19)
      | ~ v3_lattice3(X19)
      | ~ v5_orders_2(X19)
      | v2_struct_0(X19) ) ),
    inference(resolution,[],[f612,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,sK13(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f612,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X1,X2,X0)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,X2)
      | r2_yellow_0(X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f610])).

fof(f610,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ r2_hidden(X0,X2)
      | r2_yellow_0(X1,X2)
      | ~ r1_lattice3(X1,X2,X0)
      | r2_yellow_0(X1,X2)
      | ~ r1_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f486,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK7(X0,X1,X2))
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK8(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK8(X0,X1))
              & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f65,f67,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK8(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t16_yellow_0)).

fof(f486,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X2,X1)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f479])).

fof(f479,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f307,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f307,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2),X3)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,sK7(X0,X1,X2),X3)
      | ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f112,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',d8_lattice3)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f146,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ spl16_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f153,plain,
    ( l1_orders_2(sK0)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f152])).

fof(f167,plain,
    ( v5_orders_2(sK0)
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f160,plain,
    ( v3_lattice3(sK0)
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f174,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl16_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f4647,plain,
    ( ~ spl16_227
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_179
    | ~ spl16_224 ),
    inference(avatar_split_clause,[],[f4643,f2283,f1804,f173,f166,f159,f152,f2287])).

fof(f2287,plain,
    ( spl16_227
  <=> ~ m1_subset_1(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_227])])).

fof(f1804,plain,
    ( spl16_179
  <=> ~ r1_lattice3(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_179])])).

fof(f4643,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_179
    | ~ spl16_224 ),
    inference(unit_resulting_resolution,[],[f153,f174,f167,f160,f682,f683,f1805,f2284,f1726])).

fof(f1726,plain,(
    ! [X19,X17,X18] :
      ( ~ m1_subset_1(sK5(X17,X18,sK10(X17,a_2_0_yellow_0(X17,X19))),u1_struct_0(X17))
      | ~ v5_orders_2(X17)
      | v2_struct_0(X17)
      | ~ l1_orders_2(X17)
      | ~ r2_hidden(sK5(X17,X18,sK10(X17,a_2_0_yellow_0(X17,X19))),X19)
      | ~ v3_lattice3(X17)
      | ~ r1_yellow_0(X17,a_2_0_yellow_0(X17,X19))
      | r1_lattice3(X17,X18,sK10(X17,a_2_0_yellow_0(X17,X19)))
      | ~ m1_subset_1(sK10(X17,a_2_0_yellow_0(X17,X19)),u1_struct_0(X17)) ) ),
    inference(duplicate_literal_removal,[],[f1715])).

fof(f1715,plain,(
    ! [X19,X17,X18] :
      ( v2_struct_0(X17)
      | ~ v5_orders_2(X17)
      | ~ m1_subset_1(sK5(X17,X18,sK10(X17,a_2_0_yellow_0(X17,X19))),u1_struct_0(X17))
      | ~ l1_orders_2(X17)
      | ~ r2_hidden(sK5(X17,X18,sK10(X17,a_2_0_yellow_0(X17,X19))),X19)
      | ~ v3_lattice3(X17)
      | ~ m1_subset_1(sK5(X17,X18,sK10(X17,a_2_0_yellow_0(X17,X19))),u1_struct_0(X17))
      | ~ r1_yellow_0(X17,a_2_0_yellow_0(X17,X19))
      | ~ l1_orders_2(X17)
      | ~ v5_orders_2(X17)
      | r1_lattice3(X17,X18,sK10(X17,a_2_0_yellow_0(X17,X19)))
      | ~ m1_subset_1(sK10(X17,a_2_0_yellow_0(X17,X19)),u1_struct_0(X17)) ) ),
    inference(resolution,[],[f1128,f291])).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK5(X0,X2,sK10(X0,X1)))
      | ~ m1_subset_1(sK5(X0,X2,sK10(X0,X1)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X2,sK10(X0,X1))
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK5(X0,X2,sK10(X0,X1)))
      | ~ m1_subset_1(sK5(X0,X2,sK10(X0,X1)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X2,sK10(X0,X1))
      | ~ m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f116,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f116,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK10(X0,X1),X5)
      | ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK9(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK9(X0,X1,X2))
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK10(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK10(X0,X1))
              & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f70,f72,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK9(X0,X1,X2))
        & r2_lattice3(X0,X1,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK10(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK10(X0,X1))
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t15_yellow_0)).

fof(f1128,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_lattice3(X0) ) ),
    inference(duplicate_literal_removal,[],[f1124])).

fof(f1124,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f922,f401])).

fof(f401,plain,(
    ! [X14,X15,X13,X16] :
      ( m1_subset_1(sK6(X13,a_2_0_yellow_0(X14,X15),X16),u1_struct_0(X14))
      | ~ l1_orders_2(X14)
      | ~ v3_lattice3(X14)
      | ~ v5_orders_2(X14)
      | v2_struct_0(X14)
      | r2_lattice3(X13,a_2_0_yellow_0(X14,X15),X16)
      | ~ m1_subset_1(X16,u1_struct_0(X13))
      | ~ l1_orders_2(X13) ) ),
    inference(resolution,[],[f272,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',d9_lattice3)).

fof(f272,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f128,f129])).

fof(f922,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,a_2_0_yellow_0(X0,X1),X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_lattice3(X0) ) ),
    inference(duplicate_literal_removal,[],[f915])).

fof(f915,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK6(X0,a_2_0_yellow_0(X0,X1),X2),u1_struct_0(X0))
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f633,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f633,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( r1_orders_2(X2,sK6(X3,a_2_0_yellow_0(X2,X4),X5),X6)
      | ~ v3_lattice3(X2)
      | ~ v5_orders_2(X2)
      | v2_struct_0(X2)
      | r2_lattice3(X3,a_2_0_yellow_0(X2,X4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r2_hidden(X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ m1_subset_1(sK6(X3,a_2_0_yellow_0(X2,X4),X5),u1_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f632])).

fof(f632,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ l1_orders_2(X2)
      | ~ v3_lattice3(X2)
      | ~ v5_orders_2(X2)
      | v2_struct_0(X2)
      | r2_lattice3(X3,a_2_0_yellow_0(X2,X4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r2_hidden(X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | r1_orders_2(X2,sK6(X3,a_2_0_yellow_0(X2,X4),X5),X6)
      | ~ m1_subset_1(sK6(X3,a_2_0_yellow_0(X2,X4),X5),u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f407,f100])).

fof(f407,plain,(
    ! [X14,X15,X13,X16] :
      ( r1_lattice3(X13,X14,sK6(X15,a_2_0_yellow_0(X13,X14),X16))
      | ~ l1_orders_2(X13)
      | ~ v3_lattice3(X13)
      | ~ v5_orders_2(X13)
      | v2_struct_0(X13)
      | r2_lattice3(X15,a_2_0_yellow_0(X13,X14),X16)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ l1_orders_2(X15) ) ),
    inference(resolution,[],[f274,f106])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | r1_lattice3(X1,X2,X0)
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,X0)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f130,f129])).

fof(f1805,plain,
    ( ~ r1_lattice3(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_179 ),
    inference(avatar_component_clause,[],[f1804])).

fof(f683,plain,
    ( ! [X0] : m1_subset_1(sK10(sK0,X0),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f167,f153,f682,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f682,plain,
    ( ! [X0] : r1_yellow_0(sK0,X0)
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f160,f153,f167,f574])).

fof(f574,plain,(
    ! [X2,X3] :
      ( r1_yellow_0(X2,X3)
      | ~ v5_orders_2(X2)
      | ~ l1_orders_2(X2)
      | ~ v3_lattice3(X2) ) ),
    inference(global_subsumption,[],[f95,f94,f573])).

fof(f573,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK4(X0,X1))
      | r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,sK4(X0,X1))
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f493,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f493,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK9(X0,X1,sK4(X0,X1)),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0) ) ),
    inference(global_subsumption,[],[f95,f94,f492])).

fof(f492,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK4(X0,X1))
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(sK9(X0,X1,sK4(X0,X1)),u1_struct_0(X0))
      | ~ v3_lattice3(X0) ) ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK4(X0,X1))
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(sK9(X0,X1,sK4(X0,X1)),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,sK4(X0,X1))
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f319,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK9(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f319,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK9(X0,X1,sK4(X0,X2)))
      | ~ r2_lattice3(X0,X1,sK4(X0,X2))
      | ~ m1_subset_1(sK4(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(sK9(X0,X1,sK4(X0,X2)),u1_struct_0(X0))
      | ~ v3_lattice3(X0) ) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,sK4(X0,X2))
      | ~ m1_subset_1(sK4(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_lattice3(X0,X2,sK9(X0,X1,sK4(X0,X2)))
      | ~ m1_subset_1(sK9(X0,X1,sK4(X0,X2)),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f119,f96])).

fof(f96,plain,(
    ! [X6,X4,X0] :
      ( r1_orders_2(X0,sK4(X0,X4),X6)
      | ~ r2_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_orders_2(X0,X2,sK3(X0,X2))
                & r2_lattice3(X0,sK2(X0),sK3(X0,X2))
                & m1_subset_1(sK3(X0,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK2(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_orders_2(X0,sK4(X0,X4),X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,sK4(X0,X4))
              & m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,sK2(X0),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,sK2(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X2))
        & r2_lattice3(X0,X1,sK3(X0,X2))
        & m1_subset_1(sK3(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,sK4(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK4(X0,X4))
        & m1_subset_1(sK4(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',d12_lattice3)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK9(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f94,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK4(X0,X4),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    ! [X4,X0] :
      ( r2_lattice3(X0,X4,sK4(X0,X4))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f4638,plain,
    ( ~ spl16_503
    | spl16_29
    | spl16_221 ),
    inference(avatar_split_clause,[],[f4631,f2269,f264,f4636])).

fof(f4636,plain,
    ( spl16_503
  <=> ~ m1_subset_1(sK1,sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_503])])).

fof(f264,plain,
    ( spl16_29
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_29])])).

fof(f2269,plain,
    ( spl16_221
  <=> ~ r2_hidden(sK1,sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_221])])).

fof(f4631,plain,
    ( ~ m1_subset_1(sK1,sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_29
    | ~ spl16_221 ),
    inference(unit_resulting_resolution,[],[f297,f2270,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t2_subset)).

fof(f2270,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_221 ),
    inference(avatar_component_clause,[],[f2269])).

fof(f297,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl16_29 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl16_29 ),
    inference(superposition,[],[f265,f92])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t6_boole)).

fof(f265,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl16_29 ),
    inference(avatar_component_clause,[],[f264])).

fof(f4630,plain,
    ( ~ spl16_501
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_69
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4487,f1685,f830,f166,f159,f152,f4627])).

fof(f4627,plain,
    ( spl16_501
  <=> ~ r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_501])])).

fof(f830,plain,
    ( spl16_69
  <=> ~ r1_lattice3(sK0,sK1,sK10(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_69])])).

fof(f1685,plain,
    ( spl16_168
  <=> m1_subset_1(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_168])])).

fof(f4487,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_69
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f167,f682,f683,f831,f1686,f291])).

fof(f1686,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_168 ),
    inference(avatar_component_clause,[],[f1685])).

fof(f831,plain,
    ( ~ r1_lattice3(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_69 ),
    inference(avatar_component_clause,[],[f830])).

fof(f4629,plain,
    ( ~ spl16_501
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | spl16_69
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4488,f1685,f830,f264,f166,f159,f152,f4627])).

fof(f4488,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_69
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f687,f831,f683,f1686,f285])).

fof(f285,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X2,X1,sK5(X2,X3,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(sK5(X2,X3,X0),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | r1_lattice3(X2,X3,X0) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_lattice3(X2,X1,sK5(X2,X3,X0))
      | ~ m1_subset_1(sK5(X2,X3,X0),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | r1_lattice3(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f104,f103])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f687,plain,
    ( ! [X0] : r2_hidden(sK10(sK0,X0),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f167,f297,f682,f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(resolution,[],[f114,f123])).

fof(f4622,plain,
    ( spl16_486
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_106
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4489,f1685,f1678,f1200,f264,f173,f166,f159,f152,f4560])).

fof(f4560,plain,
    ( spl16_486
  <=> r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_486])])).

fof(f1200,plain,
    ( spl16_106
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,X3)
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X3)),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,X3)),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_106])])).

fof(f1678,plain,
    ( spl16_166
  <=> r2_hidden(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_166])])).

fof(f4489,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_106
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f430,f1679,f1686,f1201])).

fof(f1201,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,X3)),X2)
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X3)),u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl16_106 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f1679,plain,
    ( r2_hidden(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_166 ),
    inference(avatar_component_clause,[],[f1678])).

fof(f430,plain,
    ( ! [X0] : m1_subset_1(sK11(a_2_0_yellow_0(sK0,X0)),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(forward_demodulation,[],[f425,f426])).

fof(f426,plain,
    ( ! [X0] : sK11(a_2_0_yellow_0(sK0,X0)) = sK13(sK11(a_2_0_yellow_0(sK0,X0)),sK0,X0)
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f129])).

fof(f370,plain,
    ( ! [X0] : r2_hidden(sK11(X0),X0)
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f120,f297,f123])).

fof(f120,plain,(
    ! [X0] : m1_subset_1(sK11(X0),X0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK11(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f14,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK11(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',existence_m1_subset_1)).

fof(f425,plain,
    ( ! [X0] : m1_subset_1(sK13(sK11(a_2_0_yellow_0(sK0,X0)),sK0,X0),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f128])).

fof(f4621,plain,
    ( spl16_484
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_106
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4490,f1685,f1657,f1200,f264,f173,f166,f159,f152,f4553])).

fof(f4553,plain,
    ( spl16_484
  <=> r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_484])])).

fof(f1657,plain,
    ( spl16_160
  <=> r2_hidden(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_160])])).

fof(f4490,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_106
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f430,f1658,f1686,f1201])).

fof(f1658,plain,
    ( r2_hidden(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_160 ),
    inference(avatar_component_clause,[],[f1657])).

fof(f4620,plain,
    ( spl16_490
    | ~ spl16_4
    | ~ spl16_100
    | ~ spl16_102
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4491,f1685,f1678,f1192,f1185,f152,f4578])).

fof(f4578,plain,
    ( spl16_490
  <=> r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_490])])).

fof(f1185,plain,
    ( spl16_100
  <=> r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_100])])).

fof(f1192,plain,
    ( spl16_102
  <=> m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_102])])).

fof(f4491,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_100
    | ~ spl16_102
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f1193,f1186,f1679,f1686,f100])).

fof(f1186,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_100 ),
    inference(avatar_component_clause,[],[f1185])).

fof(f1193,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_102 ),
    inference(avatar_component_clause,[],[f1192])).

fof(f4619,plain,
    ( spl16_486
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4492,f1685,f1678,f264,f173,f166,f159,f152,f4560])).

fof(f4492,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f430,f431,f1679,f1686,f100])).

fof(f431,plain,
    ( ! [X0] : r1_lattice3(sK0,X0,sK11(a_2_0_yellow_0(sK0,X0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(forward_demodulation,[],[f424,f426])).

fof(f424,plain,
    ( ! [X0] : r1_lattice3(sK0,X0,sK13(sK11(a_2_0_yellow_0(sK0,X0)),sK0,X0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f130])).

fof(f4618,plain,
    ( spl16_484
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4493,f1685,f1678,f264,f173,f166,f159,f152,f4553])).

fof(f4493,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f430,f3284,f1679,f1686,f100])).

fof(f3284,plain,
    ( ! [X0] : r1_lattice3(sK0,X0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f160,f153,f174,f297,f370,f1859])).

fof(f1859,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X1)))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | r1_lattice3(X1,X2,X0)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1854])).

fof(f1854,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X1)))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | r1_lattice3(X1,X2,X0)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f1210,f128])).

fof(f1210,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK13(X0,X1,u1_struct_0(X1)),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X1)))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | r1_lattice3(X1,X2,X0)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1209])).

fof(f1209,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,X0)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X1)))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK13(X0,X1,u1_struct_0(X1)),u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f799,f129])).

fof(f799,plain,(
    ! [X4,X5,X3] :
      ( r1_lattice3(X3,X5,sK13(X4,X3,u1_struct_0(X3)))
      | ~ r2_hidden(X4,a_2_0_yellow_0(X3,u1_struct_0(X3)))
      | ~ v3_lattice3(X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(sK13(X4,X3,u1_struct_0(X3)),u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f795])).

fof(f795,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_orders_2(X3)
      | ~ r2_hidden(X4,a_2_0_yellow_0(X3,u1_struct_0(X3)))
      | ~ v3_lattice3(X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3)
      | r1_lattice3(X3,X5,sK13(X4,X3,u1_struct_0(X3)))
      | ~ m1_subset_1(sK13(X4,X3,u1_struct_0(X3)),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_struct_0(X3))
      | r1_lattice3(X3,X5,sK13(X4,X3,u1_struct_0(X3))) ) ),
    inference(resolution,[],[f661,f245])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f101,f123])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f661,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X1,X3,sK13(X0,X1,X2)),X2)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | r1_lattice3(X1,X3,sK13(X0,X1,X2)) ) ),
    inference(global_subsumption,[],[f128,f660])).

fof(f660,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK13(X2,X0,X3)),X3)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,a_2_0_yellow_0(X0,X3))
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X0,X1,sK13(X2,X0,X3))
      | ~ m1_subset_1(sK13(X2,X0,X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f654])).

fof(f654,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK13(X2,X0,X3)),X3)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,a_2_0_yellow_0(X0,X3))
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X0,X1,sK13(X2,X0,X3))
      | r1_lattice3(X0,X1,sK13(X2,X0,X3))
      | ~ m1_subset_1(sK13(X2,X0,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f474,f101])).

fof(f474,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5(X0,X1,sK13(X2,X0,X3)),u1_struct_0(X0))
      | ~ r2_hidden(sK5(X0,X1,sK13(X2,X0,X3)),X3)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,a_2_0_yellow_0(X0,X3))
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X0,X1,sK13(X2,X0,X3)) ) ),
    inference(global_subsumption,[],[f128,f473])).

fof(f473,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5(X0,X1,sK13(X2,X0,X3)),u1_struct_0(X0))
      | ~ r2_hidden(sK5(X0,X1,sK13(X2,X0,X3)),X3)
      | ~ m1_subset_1(sK13(X2,X0,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,a_2_0_yellow_0(X0,X3))
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X0,X1,sK13(X2,X0,X3)) ) ),
    inference(duplicate_literal_removal,[],[f466])).

fof(f466,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5(X0,X1,sK13(X2,X0,X3)),u1_struct_0(X0))
      | ~ r2_hidden(sK5(X0,X1,sK13(X2,X0,X3)),X3)
      | ~ m1_subset_1(sK13(X2,X0,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,a_2_0_yellow_0(X0,X3))
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X0,X1,sK13(X2,X0,X3))
      | ~ m1_subset_1(sK13(X2,X0,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f277,f103])).

fof(f277,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X5,sK13(X6,X5,X4),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(sK13(X6,X5,X4),u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ r2_hidden(X6,a_2_0_yellow_0(X5,X4))
      | ~ v3_lattice3(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5) ) ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | r1_orders_2(X5,sK13(X6,X5,X4),X3)
      | ~ m1_subset_1(sK13(X6,X5,X4),u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ r2_hidden(X6,a_2_0_yellow_0(X5,X4))
      | ~ l1_orders_2(X5)
      | ~ v3_lattice3(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f100,f130])).

fof(f4617,plain,
    ( spl16_480
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4494,f1685,f1678,f1427,f1353,f264,f166,f152,f4539])).

fof(f4539,plain,
    ( spl16_480
  <=> r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_480])])).

fof(f1353,plain,
    ( spl16_110
  <=> r2_yellow_0(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_110])])).

fof(f1427,plain,
    ( spl16_124
  <=> m1_subset_1(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_124])])).

fof(f4494,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f1428,f2031,f1679,f1686,f100])).

fof(f2031,plain,
    ( ! [X0] : r1_lattice3(sK0,X0,sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f153,f167,f297,f1354,f1428,f792])).

fof(f792,plain,(
    ! [X2,X3] :
      ( r1_lattice3(X2,X3,sK8(X2,u1_struct_0(X2)))
      | ~ r2_yellow_0(X2,u1_struct_0(X2))
      | ~ v5_orders_2(X2)
      | ~ l1_orders_2(X2)
      | ~ m1_subset_1(sK8(X2,u1_struct_0(X2)),u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f790])).

fof(f790,plain,(
    ! [X2,X3] :
      ( ~ l1_orders_2(X2)
      | ~ r2_yellow_0(X2,u1_struct_0(X2))
      | ~ v5_orders_2(X2)
      | r1_lattice3(X2,X3,sK8(X2,u1_struct_0(X2)))
      | ~ m1_subset_1(sK8(X2,u1_struct_0(X2)),u1_struct_0(X2))
      | ~ m1_subset_1(sK8(X2,u1_struct_0(X2)),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | v1_xboole_0(u1_struct_0(X2))
      | r1_lattice3(X2,X3,sK8(X2,u1_struct_0(X2))) ) ),
    inference(resolution,[],[f647,f245])).

fof(f647,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK8(X0,X2)),X2)
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X1,sK8(X0,X2))
      | ~ m1_subset_1(sK8(X0,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f643])).

fof(f643,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK8(X0,X2)),X2)
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X1,sK8(X0,X2))
      | ~ m1_subset_1(sK8(X0,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK8(X0,X2))
      | ~ m1_subset_1(sK8(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f416,f101])).

fof(f416,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X0,X1,sK8(X0,X2)),u1_struct_0(X0))
      | ~ r2_hidden(sK5(X0,X1,sK8(X0,X2)),X2)
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X1,sK8(X0,X2))
      | ~ m1_subset_1(sK8(X0,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f411])).

fof(f411,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(X0,X1,sK8(X0,X2)),u1_struct_0(X0))
      | ~ r2_hidden(sK5(X0,X1,sK8(X0,X2)),X2)
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X2)
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X1,sK8(X0,X2))
      | ~ m1_subset_1(sK8(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f279,f103])).

fof(f279,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X2,sK8(X2,X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l1_orders_2(X2)
      | ~ r2_yellow_0(X2,X1)
      | ~ v5_orders_2(X2) ) ),
    inference(global_subsumption,[],[f108,f278])).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_orders_2(X2,sK8(X2,X1),X0)
      | ~ m1_subset_1(sK8(X2,X1),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ r2_yellow_0(X2,X1)
      | ~ v5_orders_2(X2) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_orders_2(X2,sK8(X2,X1),X0)
      | ~ m1_subset_1(sK8(X2,X1),u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ r2_yellow_0(X2,X1)
      | ~ l1_orders_2(X2)
      | ~ v5_orders_2(X2) ) ),
    inference(resolution,[],[f100,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK8(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1354,plain,
    ( r2_yellow_0(sK0,u1_struct_0(sK0))
    | ~ spl16_110 ),
    inference(avatar_component_clause,[],[f1353])).

fof(f1428,plain,
    ( m1_subset_1(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl16_124 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f4616,plain,
    ( spl16_484
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4495,f1685,f1657,f264,f173,f166,f159,f152,f4553])).

fof(f4495,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f430,f431,f1658,f1686,f100])).

fof(f4615,plain,
    ( spl16_484
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4496,f1685,f1657,f264,f173,f166,f159,f152,f4553])).

fof(f4496,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f430,f3284,f1658,f1686,f100])).

fof(f4614,plain,
    ( spl16_480
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4497,f1685,f1657,f1427,f1353,f264,f166,f152,f4539])).

fof(f4497,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f1428,f2031,f1658,f1686,f100])).

fof(f4613,plain,
    ( spl16_498
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4498,f1685,f1678,f159,f152,f4611])).

fof(f4611,plain,
    ( spl16_498
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_498])])).

fof(f4498,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK4(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f209,f211,f1679,f1686,f104])).

fof(f211,plain,
    ( ! [X0] : r2_lattice3(sK0,X0,sK4(sK0,X0))
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f153,f160,f95])).

fof(f209,plain,
    ( ! [X0] : m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f153,f160,f94])).

fof(f4606,plain,
    ( spl16_494
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4499,f1685,f1678,f264,f159,f152,f4594])).

fof(f4594,plain,
    ( spl16_494
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK4(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_494])])).

fof(f4499,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f209,f699,f1679,f1686,f104])).

fof(f699,plain,
    ( ! [X0] : r2_lattice3(sK0,X0,sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f297,f209,f211,f594])).

fof(f594,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattice3(X3,u1_struct_0(X3),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_lattice3(X3,X5,X4)
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattice3(X3,u1_struct_0(X3),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_lattice3(X3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_struct_0(X3))
      | r2_lattice3(X3,X5,X4) ) ),
    inference(resolution,[],[f457,f246])).

fof(f246,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f105,f123])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f457,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X3)
      | ~ r2_lattice3(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f455])).

fof(f455,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X3)
      | ~ r2_lattice3(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f283,f105])).

fof(f283,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(sK6(X7,X8,X9),u1_struct_0(X7))
      | ~ r2_hidden(sK6(X7,X8,X9),X10)
      | ~ r2_lattice3(X7,X10,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_orders_2(X7)
      | r2_lattice3(X7,X8,X9) ) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(sK6(X7,X8,X9),X10)
      | ~ m1_subset_1(sK6(X7,X8,X9),u1_struct_0(X7))
      | ~ r2_lattice3(X7,X10,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_orders_2(X7)
      | r2_lattice3(X7,X8,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_orders_2(X7) ) ),
    inference(resolution,[],[f104,f107])).

fof(f4605,plain,
    ( spl16_496
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4500,f1685,f1678,f166,f159,f152,f4603])).

fof(f4603,plain,
    ( spl16_496
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_496])])).

fof(f4500,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK10(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f683,f684,f1679,f1686,f104])).

fof(f684,plain,
    ( ! [X0] : r2_lattice3(sK0,X0,sK10(sK0,X0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f167,f153,f682,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK10(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f4598,plain,
    ( spl16_492
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4501,f1685,f1678,f264,f166,f159,f152,f4586])).

fof(f4586,plain,
    ( spl16_492
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK10(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_492])])).

fof(f4501,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f683,f820,f1679,f1686,f104])).

fof(f820,plain,
    ( ! [X0] : r2_lattice3(sK0,X0,sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f297,f683,f684,f594])).

fof(f4597,plain,
    ( spl16_494
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4502,f1685,f1657,f159,f152,f4594])).

fof(f4502,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f209,f211,f1658,f1686,f104])).

fof(f4596,plain,
    ( spl16_494
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4503,f1685,f1657,f264,f159,f152,f4594])).

fof(f4503,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f209,f699,f1658,f1686,f104])).

fof(f4589,plain,
    ( spl16_492
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4504,f1685,f1657,f166,f159,f152,f4586])).

fof(f4504,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f683,f684,f1658,f1686,f104])).

fof(f4588,plain,
    ( spl16_492
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4505,f1685,f1657,f264,f166,f159,f152,f4586])).

fof(f4505,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f683,f820,f1658,f1686,f104])).

fof(f4581,plain,
    ( spl16_480
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_110
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4506,f1685,f1657,f1353,f166,f152,f4539])).

fof(f4506,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_110
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f167,f153,f1354,f1658,f1686,f279])).

fof(f4580,plain,
    ( spl16_490
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_102
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4507,f1685,f1678,f1192,f264,f173,f166,f159,f152,f145,f4578])).

fof(f4507,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_102
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f167,f146,f431,f430,f1193,f1679,f1686,f307])).

fof(f4573,plain,
    ( ~ spl16_489
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4508,f1685,f1678,f166,f152,f145,f4571])).

fof(f4571,plain,
    ( spl16_489
  <=> ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_489])])).

fof(f4508,plain,
    ( ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f167,f146,f1679,f1686,f612])).

fof(f4566,plain,
    ( spl16_480
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4509,f1685,f1678,f1427,f1353,f264,f173,f166,f159,f152,f4539])).

fof(f4509,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f2415,f1679,f1686,f639])).

fof(f639,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,a_2_0_yellow_0(X1,X2))
      | ~ r2_hidden(X0,X2)
      | r1_orders_2(X1,X3,X0)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | r1_orders_2(X1,X3,X0)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X3,a_2_0_yellow_0(X1,X2))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X3,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f470,f128])).

fof(f470,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X2)
      | r1_orders_2(X1,X0,X3)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f469])).

fof(f469,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X2)
      | ~ m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f277,f129])).

fof(f2415,plain,
    ( ! [X0] : r2_hidden(sK8(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,X0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f1428,f2031,f134])).

fof(f134,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_0_yellow_0(X1,X2))
      | ~ r1_lattice3(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ r1_lattice3(X1,X2,X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f4565,plain,
    ( spl16_486
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4510,f1685,f1678,f264,f173,f166,f159,f152,f4560])).

fof(f4510,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f1679,f1686,f639])).

fof(f4564,plain,
    ( spl16_480
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4511,f1685,f1657,f1427,f1353,f264,f173,f166,f159,f152,f4539])).

fof(f4511,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f2415,f1658,f1686,f639])).

fof(f4563,plain,
    ( spl16_484
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4512,f1685,f1657,f264,f173,f166,f159,f152,f4553])).

fof(f4512,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f1658,f1686,f639])).

fof(f4562,plain,
    ( spl16_486
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4513,f1685,f1678,f264,f173,f166,f159,f152,f4560])).

fof(f4513,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f1679,f1686,f773])).

fof(f773,plain,
    ( ! [X10,X8,X9] :
        ( r1_orders_2(X10,sK11(a_2_0_yellow_0(X10,X9)),X8)
        | ~ r2_hidden(X8,X9)
        | ~ l1_orders_2(X10)
        | ~ m1_subset_1(X8,u1_struct_0(X10))
        | ~ v3_lattice3(X10)
        | ~ v5_orders_2(X10)
        | v2_struct_0(X10) )
    | ~ spl16_29 ),
    inference(resolution,[],[f639,f370])).

fof(f4555,plain,
    ( spl16_484
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4514,f1685,f1657,f264,f173,f166,f159,f152,f4553])).

fof(f4514,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f1658,f1686,f773])).

fof(f4548,plain,
    ( spl16_482
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_166
    | ~ spl16_168
    | spl16_183 ),
    inference(avatar_split_clause,[],[f4515,f1818,f1685,f1678,f264,f173,f166,f159,f152,f4546])).

fof(f4546,plain,
    ( spl16_482
  <=> r1_orders_2(sK0,sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_482])])).

fof(f1818,plain,
    ( spl16_183
  <=> ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_183])])).

fof(f4515,plain,
    ( r1_orders_2(sK0,sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_166
    | ~ spl16_168
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f160,f153,f174,f167,f430,f1819,f1679,f1686,f776])).

fof(f776,plain,(
    ! [X24,X23,X21,X22,X20] :
      ( r1_orders_2(X22,sK6(X23,a_2_0_yellow_0(X22,X21),X24),X20)
      | ~ r2_hidden(X20,X21)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X20,u1_struct_0(X22))
      | ~ v3_lattice3(X22)
      | ~ v5_orders_2(X22)
      | v2_struct_0(X22)
      | r2_lattice3(X23,a_2_0_yellow_0(X22,X21),X24)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ l1_orders_2(X23) ) ),
    inference(resolution,[],[f639,f106])).

fof(f1819,plain,
    ( ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_183 ),
    inference(avatar_component_clause,[],[f1818])).

fof(f4541,plain,
    ( spl16_480
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4516,f1685,f1678,f1427,f1353,f264,f166,f152,f4539])).

fof(f4516,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f153,f167,f297,f1354,f1428,f1679,f1686,f1064])).

fof(f1064,plain,(
    ! [X4,X5,X3] :
      ( r1_orders_2(X3,sK8(X3,u1_struct_0(X3)),X4)
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(sK8(X3,u1_struct_0(X3)),u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ r2_hidden(X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r2_yellow_0(X3,u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f1063])).

fof(f1063,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_yellow_0(X3,u1_struct_0(X3))
      | ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(sK8(X3,u1_struct_0(X3)),u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ r2_hidden(X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | r1_orders_2(X3,sK8(X3,u1_struct_0(X3)),X4)
      | ~ m1_subset_1(sK8(X3,u1_struct_0(X3)),u1_struct_0(X3))
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f792,f100])).

fof(f4534,plain,
    ( spl16_478
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4517,f1685,f1678,f173,f166,f159,f152,f4532])).

fof(f4532,plain,
    ( spl16_478
  <=> r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_478])])).

fof(f4517,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_166
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f1679,f1686,f1128])).

fof(f4527,plain,
    ( spl16_476
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(avatar_split_clause,[],[f4518,f1685,f1657,f173,f166,f159,f152,f4525])).

fof(f4525,plain,
    ( spl16_476
  <=> r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_476])])).

fof(f4518,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_160
    | ~ spl16_168 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f1658,f1686,f1128])).

fof(f4480,plain,
    ( spl16_474
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_465 ),
    inference(avatar_split_clause,[],[f4442,f4430,f166,f159,f152,f4478])).

fof(f4478,plain,
    ( spl16_474
  <=> m1_subset_1(sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_474])])).

fof(f4430,plain,
    ( spl16_465
  <=> ~ r1_lattice3(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_465])])).

fof(f4442,plain,
    ( m1_subset_1(sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_465 ),
    inference(unit_resulting_resolution,[],[f153,f683,f4431,f101])).

fof(f4431,plain,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_465 ),
    inference(avatar_component_clause,[],[f4430])).

fof(f4473,plain,
    ( spl16_470
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_465 ),
    inference(avatar_split_clause,[],[f4443,f4430,f166,f159,f152,f4462])).

fof(f4462,plain,
    ( spl16_470
  <=> r2_hidden(sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_470])])).

fof(f4443,plain,
    ( r2_hidden(sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_465 ),
    inference(unit_resulting_resolution,[],[f153,f683,f4431,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f4472,plain,
    ( ~ spl16_473
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_465 ),
    inference(avatar_split_clause,[],[f4444,f4430,f166,f159,f152,f4470])).

fof(f4470,plain,
    ( spl16_473
  <=> ~ r1_orders_2(sK0,sK10(sK0,u1_struct_0(sK0)),sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_473])])).

fof(f4444,plain,
    ( ~ r1_orders_2(sK0,sK10(sK0,u1_struct_0(sK0)),sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_465 ),
    inference(unit_resulting_resolution,[],[f153,f683,f4431,f103])).

fof(f4465,plain,
    ( ~ spl16_469
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_465 ),
    inference(avatar_split_clause,[],[f4445,f4430,f166,f159,f152,f4455])).

fof(f4455,plain,
    ( spl16_469
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_469])])).

fof(f4445,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_465 ),
    inference(unit_resulting_resolution,[],[f153,f683,f4431,f230])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f102,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',antisymmetry_r2_hidden)).

fof(f4464,plain,
    ( spl16_470
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | spl16_465 ),
    inference(avatar_split_clause,[],[f4446,f4430,f264,f166,f159,f152,f4462])).

fof(f4446,plain,
    ( r2_hidden(sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_465 ),
    inference(unit_resulting_resolution,[],[f153,f297,f683,f4431,f245])).

fof(f4457,plain,
    ( ~ spl16_469
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | spl16_465 ),
    inference(avatar_split_clause,[],[f4448,f4430,f264,f166,f159,f152,f4455])).

fof(f4448,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_465 ),
    inference(unit_resulting_resolution,[],[f153,f297,f683,f4431,f409])).

fof(f409,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X1),sK5(X1,X2,X0))
      | ~ l1_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | r1_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f245,f121])).

fof(f4441,plain,
    ( ~ spl16_467
    | spl16_29
    | spl16_157 ),
    inference(avatar_split_clause,[],[f4434,f1643,f264,f4439])).

fof(f4439,plain,
    ( spl16_467
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_467])])).

fof(f1643,plain,
    ( spl16_157
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_157])])).

fof(f4434,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_29
    | ~ spl16_157 ),
    inference(unit_resulting_resolution,[],[f297,f1644,f123])).

fof(f1644,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_157 ),
    inference(avatar_component_clause,[],[f1643])).

fof(f4433,plain,
    ( spl16_10
    | ~ spl16_9
    | ~ spl16_7
    | ~ spl16_5
    | ~ spl16_73
    | ~ spl16_465
    | spl16_399 ),
    inference(avatar_split_clause,[],[f4418,f3312,f4430,f844,f149,f156,f163,f170])).

fof(f170,plain,
    ( spl16_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f163,plain,
    ( spl16_9
  <=> ~ v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f156,plain,
    ( spl16_7
  <=> ~ v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).

fof(f149,plain,
    ( spl16_5
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f844,plain,
    ( spl16_73
  <=> ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_73])])).

fof(f3312,plain,
    ( spl16_399
  <=> ~ r2_hidden(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_399])])).

fof(f4418,plain,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0)))
    | ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_399 ),
    inference(resolution,[],[f3313,f134])).

fof(f3313,plain,
    ( ~ r2_hidden(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_399 ),
    inference(avatar_component_clause,[],[f3312])).

fof(f4432,plain,
    ( ~ spl16_465
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_399 ),
    inference(avatar_split_clause,[],[f4416,f3312,f173,f166,f159,f152,f4430])).

fof(f4416,plain,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_399 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f683,f3313,f134])).

fof(f4425,plain,
    ( ~ spl16_463
    | spl16_29
    | spl16_399 ),
    inference(avatar_split_clause,[],[f4417,f3312,f264,f4423])).

fof(f4423,plain,
    ( spl16_463
  <=> ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_463])])).

fof(f4417,plain,
    ( ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_29
    | ~ spl16_399 ),
    inference(unit_resulting_resolution,[],[f297,f3313,f123])).

fof(f4406,plain,
    ( ~ spl16_461
    | spl16_29
    | spl16_231 ),
    inference(avatar_split_clause,[],[f4398,f2311,f264,f4404])).

fof(f4404,plain,
    ( spl16_461
  <=> ~ m1_subset_1(sK4(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_461])])).

fof(f2311,plain,
    ( spl16_231
  <=> ~ r2_hidden(sK4(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_231])])).

fof(f4398,plain,
    ( ~ m1_subset_1(sK4(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_29
    | ~ spl16_231 ),
    inference(unit_resulting_resolution,[],[f297,f2312,f123])).

fof(f2312,plain,
    ( ~ r2_hidden(sK4(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_231 ),
    inference(avatar_component_clause,[],[f2311])).

fof(f4396,plain,
    ( ~ spl16_459
    | spl16_29
    | spl16_217 ),
    inference(avatar_split_clause,[],[f4388,f2255,f264,f4394])).

fof(f4394,plain,
    ( spl16_459
  <=> ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_459])])).

fof(f2255,plain,
    ( spl16_217
  <=> ~ r2_hidden(sK10(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_217])])).

fof(f4388,plain,
    ( ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_29
    | ~ spl16_217 ),
    inference(unit_resulting_resolution,[],[f297,f2256,f123])).

fof(f2256,plain,
    ( ~ r2_hidden(sK10(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_217 ),
    inference(avatar_component_clause,[],[f2255])).

fof(f4386,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_447 ),
    inference(avatar_contradiction_clause,[],[f4378])).

fof(f4378,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_447 ),
    inference(unit_resulting_resolution,[],[f444,f4327,f122])).

fof(f4327,plain,
    ( ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_447 ),
    inference(avatar_component_clause,[],[f4326])).

fof(f4326,plain,
    ( spl16_447
  <=> ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_447])])).

fof(f444,plain,
    ( ! [X0] : r2_hidden(sK11(a_2_0_yellow_0(sK0,X0)),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(forward_demodulation,[],[f440,f426])).

fof(f440,plain,
    ( ! [X0] : r2_hidden(sK13(sK11(a_2_0_yellow_0(sK0,X0)),sK0,X0),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f160,f153,f174,f167,f370,f297,f270])).

fof(f270,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2)) ) ),
    inference(resolution,[],[f128,f123])).

fof(f4385,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_447 ),
    inference(avatar_contradiction_clause,[],[f4376])).

fof(f4376,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_447 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f4327,f272])).

fof(f4384,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_447 ),
    inference(avatar_contradiction_clause,[],[f4370])).

fof(f4370,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_447 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f4327,f429])).

fof(f429,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(sK11(a_2_0_yellow_0(X3,X4)),u1_struct_0(X3))
        | ~ l1_orders_2(X3)
        | ~ v3_lattice3(X3)
        | ~ v5_orders_2(X3)
        | v2_struct_0(X3) )
    | ~ spl16_29 ),
    inference(resolution,[],[f370,f272])).

fof(f4383,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_447 ),
    inference(avatar_contradiction_clause,[],[f4365])).

fof(f4365,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_447 ),
    inference(unit_resulting_resolution,[],[f430,f4327])).

fof(f4382,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_447 ),
    inference(avatar_contradiction_clause,[],[f4379])).

fof(f4379,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_447 ),
    inference(resolution,[],[f4327,f430])).

fof(f4364,plain,
    ( spl16_456
    | ~ spl16_166 ),
    inference(avatar_split_clause,[],[f4346,f1678,f4362])).

fof(f4362,plain,
    ( spl16_456
  <=> m1_subset_1(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_456])])).

fof(f4346,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_166 ),
    inference(unit_resulting_resolution,[],[f1679,f122])).

fof(f4357,plain,
    ( ~ spl16_455
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_166 ),
    inference(avatar_split_clause,[],[f4347,f1678,f173,f166,f159,f152,f145,f4355])).

fof(f4355,plain,
    ( spl16_455
  <=> ~ r2_hidden(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_455])])).

fof(f4347,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_166 ),
    inference(unit_resulting_resolution,[],[f174,f160,f167,f153,f146,f1679,f1759])).

fof(f4343,plain,
    ( ~ spl16_453
    | spl16_29
    | spl16_163 ),
    inference(avatar_split_clause,[],[f4336,f1664,f264,f4341])).

fof(f4341,plain,
    ( spl16_453
  <=> ~ m1_subset_1(sK1,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_453])])).

fof(f1664,plain,
    ( spl16_163
  <=> ~ r2_hidden(sK1,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_163])])).

fof(f4336,plain,
    ( ~ m1_subset_1(sK1,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_29
    | ~ spl16_163 ),
    inference(unit_resulting_resolution,[],[f297,f1665,f123])).

fof(f1665,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_163 ),
    inference(avatar_component_clause,[],[f1664])).

fof(f4335,plain,
    ( ~ spl16_5
    | ~ spl16_447
    | spl16_450
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4250,f264,f173,f166,f159,f152,f4333,f4326,f149])).

fof(f4333,plain,
    ( spl16_450
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X1,X2)
        | r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_450])])).

fof(f4250,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),X1)
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(resolution,[],[f3284,f100])).

fof(f4331,plain,
    ( ~ spl16_447
    | spl16_448
    | ~ spl16_9
    | ~ spl16_5
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4249,f264,f173,f166,f159,f152,f149,f163,f4329,f4326])).

fof(f4329,plain,
    ( spl16_448
  <=> ! [X0] :
        ( ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),X0)
        | r2_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_448])])).

fof(f4249,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),X0)
        | r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(resolution,[],[f3284,f612])).

fof(f4321,plain,
    ( spl16_444
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4229,f264,f173,f166,f159,f152,f145,f4319])).

fof(f4319,plain,
    ( spl16_444
  <=> m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_444])])).

fof(f4229,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f430,f3284,f111])).

fof(f4314,plain,
    ( spl16_442
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4230,f264,f173,f166,f159,f152,f145,f4312])).

fof(f4312,plain,
    ( spl16_442
  <=> r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_442])])).

fof(f4230,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f430,f3284,f112])).

fof(f4307,plain,
    ( ~ spl16_441
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4231,f264,f173,f166,f159,f152,f145,f4305])).

fof(f4305,plain,
    ( spl16_441
  <=> ~ r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_441])])).

fof(f4231,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f430,f3284,f113])).

fof(f4300,plain,
    ( spl16_438
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4234,f264,f173,f166,f159,f152,f145,f4298])).

fof(f4298,plain,
    ( spl16_438
  <=> r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_438])])).

fof(f4234,plain,
    ( r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f146,f153,f167,f297,f430,f3284,f305])).

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(resolution,[],[f111,f123])).

fof(f4293,plain,
    ( ~ spl16_437
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4235,f264,f173,f166,f159,f152,f145,f4291])).

fof(f4291,plain,
    ( spl16_437
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_437])])).

fof(f4235,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f146,f167,f297,f430,f3284,f445])).

fof(f445,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X0),sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f305,f121])).

fof(f4286,plain,
    ( ~ spl16_435
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4236,f264,f173,f166,f159,f152,f145,f4284])).

fof(f4284,plain,
    ( spl16_435
  <=> ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_435])])).

fof(f4236,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f146,f153,f1707,f430,f3284,f462])).

fof(f462,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X2)
      | r2_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f460])).

fof(f460,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X3)
      | r2_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X3,X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f311,f111])).

fof(f311,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X3)
      | r2_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X3)
      | ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f113,f104])).

fof(f1707,plain,
    ( ! [X0] : r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK11(a_2_0_yellow_0(sK0,X0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f444,f430,f1128])).

fof(f4279,plain,
    ( ~ spl16_433
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4237,f264,f173,f166,f159,f152,f145,f4277])).

fof(f4277,plain,
    ( spl16_433
  <=> ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_433])])).

fof(f4237,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f146,f153,f1706,f430,f3284,f462])).

fof(f1706,plain,
    ( ! [X0] : r2_lattice3(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,X0)),sK11(a_2_0_yellow_0(sK0,X0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f370,f430,f1128])).

fof(f4272,plain,
    ( ~ spl16_431
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4238,f264,f173,f166,f159,f152,f145,f4270])).

fof(f4270,plain,
    ( spl16_431
  <=> ~ r2_lattice3(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_431])])).

fof(f4238,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f167,f146,f297,f430,f3284,f605])).

fof(f605,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X1,u1_struct_0(X1),X0)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ r1_lattice3(X1,X2,X0)
      | r2_yellow_0(X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f603])).

fof(f603,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ r1_lattice3(X1,X2,X0)
      | r2_yellow_0(X1,X2)
      | ~ r2_lattice3(X1,u1_struct_0(X1),X0)
      | ~ r1_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | r2_yellow_0(X1,X2) ) ),
    inference(resolution,[],[f462,f305])).

fof(f4265,plain,
    ( ~ spl16_429
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4243,f264,f173,f166,f159,f152,f145,f4263])).

fof(f4263,plain,
    ( spl16_429
  <=> ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_429])])).

fof(f4243,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f146,f167,f153,f430,f3284,f1090])).

fof(f1090,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X1)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f1088])).

fof(f1088,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f729,f111])).

fof(f729,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(sK7(X8,X9,X10),u1_struct_0(X8))
      | ~ v5_orders_2(X8)
      | ~ r2_hidden(sK7(X8,X9,X10),X9)
      | r2_yellow_0(X8,X9)
      | ~ l1_orders_2(X8)
      | ~ r1_lattice3(X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X8)) ) ),
    inference(duplicate_literal_removal,[],[f720])).

fof(f720,plain,(
    ! [X10,X8,X9] :
      ( ~ l1_orders_2(X8)
      | ~ v5_orders_2(X8)
      | ~ r2_hidden(sK7(X8,X9,X10),X9)
      | r2_yellow_0(X8,X9)
      | ~ m1_subset_1(sK7(X8,X9,X10),u1_struct_0(X8))
      | r2_yellow_0(X8,X9)
      | ~ r1_lattice3(X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v5_orders_2(X8) ) ),
    inference(resolution,[],[f612,f112])).

fof(f4258,plain,
    ( ~ spl16_427
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f4244,f264,f173,f166,f159,f152,f145,f4256])).

fof(f4256,plain,
    ( spl16_427
  <=> ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_427])])).

fof(f4244,plain,
    ( ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f174,f160,f153,f146,f167,f430,f3284,f1205])).

fof(f1205,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | r2_yellow_0(X0,X1)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f1203])).

fof(f1203,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X2)
      | r2_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f896,f111])).

fof(f896,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X2)
      | r2_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f895])).

fof(f895,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X2)
      | r2_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f604,f112])).

fof(f604,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_lattice3(X6,X7,sK7(X4,X5,X3))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | ~ r1_lattice3(X4,X5,X3)
      | r2_yellow_0(X4,X5)
      | ~ r2_lattice3(X4,a_2_0_yellow_0(X6,X7),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(sK7(X4,X5,X3),u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v3_lattice3(X6)
      | ~ v5_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f462,f134])).

fof(f4131,plain,
    ( ~ spl16_425
    | spl16_29
    | spl16_403 ),
    inference(avatar_split_clause,[],[f4124,f3420,f264,f4129])).

fof(f4129,plain,
    ( spl16_425
  <=> ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_425])])).

fof(f3420,plain,
    ( spl16_403
  <=> ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_403])])).

fof(f4124,plain,
    ( ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_29
    | ~ spl16_403 ),
    inference(unit_resulting_resolution,[],[f297,f3421,f123])).

fof(f3421,plain,
    ( ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_403 ),
    inference(avatar_component_clause,[],[f3420])).

fof(f3682,plain,
    ( ~ spl16_423
    | spl16_407 ),
    inference(avatar_split_clause,[],[f3674,f3464,f3679])).

fof(f3679,plain,
    ( spl16_423
  <=> ~ r2_hidden(sK11(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_423])])).

fof(f3464,plain,
    ( spl16_407
  <=> ~ m1_subset_1(sK11(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_407])])).

fof(f3674,plain,
    ( ~ r2_hidden(sK11(sK1),u1_struct_0(sK0))
    | ~ spl16_407 ),
    inference(resolution,[],[f3465,f122])).

fof(f3465,plain,
    ( ~ m1_subset_1(sK11(sK1),u1_struct_0(sK0))
    | ~ spl16_407 ),
    inference(avatar_component_clause,[],[f3464])).

fof(f3681,plain,
    ( ~ spl16_423
    | spl16_407 ),
    inference(avatar_split_clause,[],[f3673,f3464,f3679])).

fof(f3673,plain,
    ( ~ r2_hidden(sK11(sK1),u1_struct_0(sK0))
    | ~ spl16_407 ),
    inference(unit_resulting_resolution,[],[f3465,f122])).

fof(f3662,plain,
    ( spl16_10
    | ~ spl16_9
    | ~ spl16_7
    | ~ spl16_5
    | spl16_420
    | ~ spl16_184 ),
    inference(avatar_split_clause,[],[f3632,f1822,f3660,f149,f156,f163,f170])).

fof(f3660,plain,
    ( spl16_420
  <=> ! [X86,X87] :
        ( v2_struct_0(X86)
        | r2_yellow_0(sK0,a_2_0_yellow_0(X86,X87))
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X86,X87))),u1_struct_0(sK0))
        | ~ r2_hidden(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X86,X87))),a_2_0_yellow_0(sK0,u1_struct_0(X86)))
        | ~ v5_orders_2(X86)
        | ~ v3_lattice3(X86)
        | ~ l1_orders_2(X86)
        | v1_xboole_0(u1_struct_0(X86)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_420])])).

fof(f1822,plain,
    ( spl16_184
  <=> ! [X24] :
        ( ~ r1_lattice3(sK0,X24,sK10(sK0,a_2_0_yellow_0(sK0,X24)))
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,X24)),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X24) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_184])])).

fof(f3632,plain,
    ( ! [X87,X86] :
        ( v2_struct_0(X86)
        | v1_xboole_0(u1_struct_0(X86))
        | ~ l1_orders_2(X86)
        | ~ v3_lattice3(X86)
        | ~ v5_orders_2(X86)
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X86,X87))),a_2_0_yellow_0(sK0,u1_struct_0(X86)))
        | ~ v3_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X86,X87))),u1_struct_0(sK0))
        | r2_yellow_0(sK0,a_2_0_yellow_0(X86,X87)) )
    | ~ spl16_184 ),
    inference(resolution,[],[f1967,f1823])).

fof(f1823,plain,
    ( ! [X24] :
        ( ~ r1_lattice3(sK0,X24,sK10(sK0,a_2_0_yellow_0(sK0,X24)))
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,X24)),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X24) )
    | ~ spl16_184 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f1967,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X3,a_2_0_yellow_0(X1,u1_struct_0(X0)))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f1962])).

fof(f1962,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | r1_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X3,a_2_0_yellow_0(X1,u1_struct_0(X0)))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X3,a_2_0_yellow_0(X1,u1_struct_0(X0)))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f1309,f128])).

fof(f1309,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK13(X0,X1,u1_struct_0(X2)),u1_struct_0(X1))
      | ~ v5_orders_2(X2)
      | v2_struct_0(X2)
      | v1_xboole_0(u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ v3_lattice3(X2)
      | r1_lattice3(X1,a_2_0_yellow_0(X2,X3),X0)
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X2)))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f1308])).

fof(f1308,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X1,a_2_0_yellow_0(X2,X3),X0)
      | ~ v5_orders_2(X2)
      | v2_struct_0(X2)
      | v1_xboole_0(u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ v3_lattice3(X2)
      | ~ m1_subset_1(sK13(X0,X1,u1_struct_0(X2)),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X2)))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,u1_struct_0(X2)))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f812,f129])).

fof(f812,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_lattice3(X8,a_2_0_yellow_0(X7,X9),sK13(X10,X8,u1_struct_0(X7)))
      | ~ v5_orders_2(X7)
      | v2_struct_0(X7)
      | v1_xboole_0(u1_struct_0(X7))
      | ~ l1_orders_2(X7)
      | ~ v3_lattice3(X7)
      | ~ m1_subset_1(sK13(X10,X8,u1_struct_0(X7)),u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ r2_hidden(X10,a_2_0_yellow_0(X8,u1_struct_0(X7)))
      | ~ v3_lattice3(X8)
      | ~ v5_orders_2(X8)
      | v2_struct_0(X8) ) ),
    inference(duplicate_literal_removal,[],[f811])).

fof(f811,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ v3_lattice3(X7)
      | ~ v5_orders_2(X7)
      | v2_struct_0(X7)
      | v1_xboole_0(u1_struct_0(X7))
      | ~ l1_orders_2(X7)
      | r1_lattice3(X8,a_2_0_yellow_0(X7,X9),sK13(X10,X8,u1_struct_0(X7)))
      | ~ m1_subset_1(sK13(X10,X8,u1_struct_0(X7)),u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ r2_hidden(X10,a_2_0_yellow_0(X8,u1_struct_0(X7)))
      | ~ v3_lattice3(X8)
      | ~ v5_orders_2(X8)
      | v2_struct_0(X8)
      | r1_lattice3(X8,a_2_0_yellow_0(X7,X9),sK13(X10,X8,u1_struct_0(X7))) ) ),
    inference(resolution,[],[f588,f661])).

fof(f588,plain,(
    ! [X14,X12,X13,X11] :
      ( r2_hidden(sK5(X12,a_2_0_yellow_0(X11,X13),X14),u1_struct_0(X11))
      | ~ v3_lattice3(X11)
      | ~ v5_orders_2(X11)
      | v2_struct_0(X11)
      | v1_xboole_0(u1_struct_0(X11))
      | ~ l1_orders_2(X11)
      | r1_lattice3(X12,a_2_0_yellow_0(X11,X13),X14)
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ l1_orders_2(X12) ) ),
    inference(resolution,[],[f443,f102])).

fof(f443,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | r2_hidden(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f270,f129])).

fof(f3658,plain,
    ( spl16_10
    | ~ spl16_9
    | ~ spl16_7
    | ~ spl16_5
    | spl16_418
    | ~ spl16_74 ),
    inference(avatar_split_clause,[],[f3631,f847,f3656,f149,f156,f163,f170])).

fof(f3656,plain,
    ( spl16_418
  <=> ! [X84,X85] :
        ( v2_struct_0(X84)
        | r2_yellow_0(sK0,a_2_0_yellow_0(X84,X85))
        | ~ r2_hidden(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(X84)))
        | ~ v5_orders_2(X84)
        | ~ v3_lattice3(X84)
        | ~ l1_orders_2(X84)
        | v1_xboole_0(u1_struct_0(X84)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_418])])).

fof(f847,plain,
    ( spl16_74
  <=> ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK10(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_74])])).

fof(f3631,plain,
    ( ! [X85,X84] :
        ( v2_struct_0(X84)
        | v1_xboole_0(u1_struct_0(X84))
        | ~ l1_orders_2(X84)
        | ~ v3_lattice3(X84)
        | ~ v5_orders_2(X84)
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(X84)))
        | ~ v3_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | r2_yellow_0(sK0,a_2_0_yellow_0(X84,X85)) )
    | ~ spl16_74 ),
    inference(resolution,[],[f1967,f848])).

fof(f848,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,X1,sK10(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X1) )
    | ~ spl16_74 ),
    inference(avatar_component_clause,[],[f847])).

fof(f3654,plain,
    ( spl16_10
    | ~ spl16_9
    | ~ spl16_7
    | ~ spl16_5
    | spl16_416
    | ~ spl16_64 ),
    inference(avatar_split_clause,[],[f3630,f766,f3652,f149,f156,f163,f170])).

fof(f3652,plain,
    ( spl16_416
  <=> ! [X82,X83] :
        ( v2_struct_0(X82)
        | r2_yellow_0(sK0,a_2_0_yellow_0(X82,X83))
        | ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(X82)))
        | ~ v5_orders_2(X82)
        | ~ v3_lattice3(X82)
        | ~ l1_orders_2(X82)
        | v1_xboole_0(u1_struct_0(X82)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_416])])).

fof(f766,plain,
    ( spl16_64
  <=> ! [X7] :
        ( ~ r1_lattice3(sK0,X7,sK4(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_64])])).

fof(f3630,plain,
    ( ! [X83,X82] :
        ( v2_struct_0(X82)
        | v1_xboole_0(u1_struct_0(X82))
        | ~ l1_orders_2(X82)
        | ~ v3_lattice3(X82)
        | ~ v5_orders_2(X82)
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(X82)))
        | ~ v3_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | r2_yellow_0(sK0,a_2_0_yellow_0(X82,X83)) )
    | ~ spl16_64 ),
    inference(resolution,[],[f1967,f767])).

fof(f767,plain,
    ( ! [X7] :
        ( ~ r1_lattice3(sK0,X7,sK4(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X7) )
    | ~ spl16_64 ),
    inference(avatar_component_clause,[],[f766])).

fof(f3592,plain,
    ( spl16_22
    | ~ spl16_5
    | spl16_414
    | ~ spl16_184 ),
    inference(avatar_split_clause,[],[f3565,f1822,f3590,f149,f220])).

fof(f220,plain,
    ( spl16_22
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f3590,plain,
    ( spl16_414
  <=> ! [X67] :
        ( r2_yellow_0(X67,u1_struct_0(sK0))
        | r2_yellow_0(sK0,a_2_0_yellow_0(X67,u1_struct_0(sK0)))
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X67,u1_struct_0(sK0)))),u1_struct_0(sK0))
        | ~ v5_orders_2(X67)
        | v2_struct_0(X67)
        | ~ v3_lattice3(X67)
        | ~ l1_orders_2(X67) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_414])])).

fof(f3565,plain,
    ( ! [X67] :
        ( r2_yellow_0(X67,u1_struct_0(sK0))
        | ~ l1_orders_2(X67)
        | ~ v3_lattice3(X67)
        | v2_struct_0(X67)
        | ~ v5_orders_2(X67)
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X67,u1_struct_0(sK0)))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_yellow_0(sK0,a_2_0_yellow_0(X67,u1_struct_0(sK0))) )
    | ~ spl16_184 ),
    inference(duplicate_literal_removal,[],[f3564])).

fof(f3564,plain,
    ( ! [X67] :
        ( r2_yellow_0(X67,u1_struct_0(sK0))
        | ~ l1_orders_2(X67)
        | ~ v3_lattice3(X67)
        | v2_struct_0(X67)
        | ~ v5_orders_2(X67)
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X67,u1_struct_0(sK0)))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X67,u1_struct_0(sK0)))),u1_struct_0(sK0))
        | r2_yellow_0(sK0,a_2_0_yellow_0(X67,u1_struct_0(sK0))) )
    | ~ spl16_184 ),
    inference(resolution,[],[f1899,f1823])).

fof(f1899,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,a_2_0_yellow_0(X0,u1_struct_0(X1)),X2)
      | r2_yellow_0(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1895])).

fof(f1895,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | r2_yellow_0(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X1,a_2_0_yellow_0(X0,u1_struct_0(X1)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | r1_lattice3(X1,a_2_0_yellow_0(X0,u1_struct_0(X1)),X2) ) ),
    inference(resolution,[],[f1304,f245])).

fof(f1304,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X1,a_2_0_yellow_0(X0,X2),X3),X2)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f1300])).

fof(f1300,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(sK5(X1,a_2_0_yellow_0(X0,X2),X3),X2)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f731,f400])).

fof(f400,plain,(
    ! [X12,X10,X11,X9] :
      ( m1_subset_1(sK5(X9,a_2_0_yellow_0(X10,X11),X12),u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v3_lattice3(X10)
      | ~ v5_orders_2(X10)
      | v2_struct_0(X10)
      | r1_lattice3(X9,a_2_0_yellow_0(X10,X11),X12)
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ l1_orders_2(X9) ) ),
    inference(resolution,[],[f272,f102])).

fof(f731,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5(X1,a_2_0_yellow_0(X0,X2),X3),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(sK5(X1,a_2_0_yellow_0(X0,X2),X3),X2)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f718])).

fof(f718,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(sK5(X1,a_2_0_yellow_0(X0,X2),X3),X2)
      | r2_yellow_0(X0,X2)
      | ~ m1_subset_1(sK5(X1,a_2_0_yellow_0(X0,X2),X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f612,f406])).

fof(f406,plain,(
    ! [X12,X10,X11,X9] :
      ( r1_lattice3(X9,X10,sK5(X11,a_2_0_yellow_0(X9,X10),X12))
      | ~ l1_orders_2(X9)
      | ~ v3_lattice3(X9)
      | ~ v5_orders_2(X9)
      | v2_struct_0(X9)
      | r1_lattice3(X11,a_2_0_yellow_0(X9,X10),X12)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | ~ l1_orders_2(X11) ) ),
    inference(resolution,[],[f274,f102])).

fof(f3588,plain,
    ( spl16_22
    | ~ spl16_5
    | ~ spl16_73
    | spl16_412
    | ~ spl16_74 ),
    inference(avatar_split_clause,[],[f3563,f847,f3585,f844,f149,f220])).

fof(f3585,plain,
    ( spl16_412
  <=> ! [X65] :
        ( r2_yellow_0(X65,u1_struct_0(sK0))
        | r2_yellow_0(sK0,a_2_0_yellow_0(X65,u1_struct_0(sK0)))
        | ~ v5_orders_2(X65)
        | v2_struct_0(X65)
        | ~ v3_lattice3(X65)
        | ~ l1_orders_2(X65) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_412])])).

fof(f3563,plain,
    ( ! [X66] :
        ( r2_yellow_0(X66,u1_struct_0(sK0))
        | ~ l1_orders_2(X66)
        | ~ v3_lattice3(X66)
        | v2_struct_0(X66)
        | ~ v5_orders_2(X66)
        | ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_yellow_0(sK0,a_2_0_yellow_0(X66,u1_struct_0(sK0))) )
    | ~ spl16_74 ),
    inference(resolution,[],[f1899,f848])).

fof(f3587,plain,
    ( spl16_22
    | ~ spl16_5
    | ~ spl16_63
    | spl16_412
    | ~ spl16_64 ),
    inference(avatar_split_clause,[],[f3562,f766,f3585,f763,f149,f220])).

fof(f763,plain,
    ( spl16_63
  <=> ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_63])])).

fof(f3562,plain,
    ( ! [X65] :
        ( r2_yellow_0(X65,u1_struct_0(sK0))
        | ~ l1_orders_2(X65)
        | ~ v3_lattice3(X65)
        | v2_struct_0(X65)
        | ~ v5_orders_2(X65)
        | ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_yellow_0(sK0,a_2_0_yellow_0(X65,u1_struct_0(sK0))) )
    | ~ spl16_64 ),
    inference(resolution,[],[f1899,f767])).

fof(f3503,plain,
    ( spl16_22
    | ~ spl16_5
    | ~ spl16_89
    | spl16_410
    | ~ spl16_154 ),
    inference(avatar_split_clause,[],[f3486,f1600,f3501,f987,f149,f220])).

fof(f987,plain,
    ( spl16_89
  <=> ~ m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_89])])).

fof(f3501,plain,
    ( spl16_410
  <=> ! [X37] :
        ( r2_yellow_0(X37,u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(X37,u1_struct_0(sK0)))
        | ~ v5_orders_2(X37)
        | v2_struct_0(X37)
        | ~ v3_lattice3(X37)
        | ~ l1_orders_2(X37) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_410])])).

fof(f1600,plain,
    ( spl16_154
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),X0)
        | ~ r2_lattice3(sK0,X0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_154])])).

fof(f3486,plain,
    ( ! [X37] :
        ( r2_yellow_0(X37,u1_struct_0(sK0))
        | ~ l1_orders_2(X37)
        | ~ v3_lattice3(X37)
        | v2_struct_0(X37)
        | ~ v5_orders_2(X37)
        | ~ m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(X37,u1_struct_0(sK0))) )
    | ~ spl16_154 ),
    inference(resolution,[],[f1894,f1601])).

fof(f1601,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
        | ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),X0) )
    | ~ spl16_154 ),
    inference(avatar_component_clause,[],[f1600])).

fof(f1894,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,a_2_0_yellow_0(X0,u1_struct_0(X1)),X2)
      | r2_yellow_0(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1890])).

fof(f1890,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | r2_yellow_0(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X1,a_2_0_yellow_0(X0,u1_struct_0(X1)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | r2_lattice3(X1,a_2_0_yellow_0(X0,u1_struct_0(X1)),X2) ) ),
    inference(resolution,[],[f1299,f246])).

fof(f1299,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK6(X1,a_2_0_yellow_0(X0,X2),X3),X2)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f1295])).

fof(f1295,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(sK6(X1,a_2_0_yellow_0(X0,X2),X3),X2)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X1,a_2_0_yellow_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f730,f401])).

fof(f730,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK6(X5,a_2_0_yellow_0(X4,X6),X7),u1_struct_0(X4))
      | ~ v5_orders_2(X4)
      | ~ r2_hidden(sK6(X5,a_2_0_yellow_0(X4,X6),X7),X6)
      | r2_yellow_0(X4,X6)
      | ~ l1_orders_2(X4)
      | ~ v3_lattice3(X4)
      | v2_struct_0(X4)
      | r2_lattice3(X5,a_2_0_yellow_0(X4,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ l1_orders_2(X5) ) ),
    inference(duplicate_literal_removal,[],[f719])).

fof(f719,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | ~ r2_hidden(sK6(X5,a_2_0_yellow_0(X4,X6),X7),X6)
      | r2_yellow_0(X4,X6)
      | ~ m1_subset_1(sK6(X5,a_2_0_yellow_0(X4,X6),X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v3_lattice3(X4)
      | ~ v5_orders_2(X4)
      | v2_struct_0(X4)
      | r2_lattice3(X5,a_2_0_yellow_0(X4,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ l1_orders_2(X5) ) ),
    inference(resolution,[],[f612,f407])).

fof(f3472,plain,
    ( spl16_10
    | ~ spl16_9
    | ~ spl16_7
    | ~ spl16_5
    | ~ spl16_407
    | ~ spl16_409
    | spl16_393 ),
    inference(avatar_split_clause,[],[f3452,f3194,f3470,f3464,f149,f156,f163,f170])).

fof(f3470,plain,
    ( spl16_409
  <=> ~ r1_lattice3(sK0,sK1,sK11(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_409])])).

fof(f3194,plain,
    ( spl16_393
  <=> ~ r2_hidden(sK11(sK1),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_393])])).

fof(f3452,plain,
    ( ~ r1_lattice3(sK0,sK1,sK11(sK1))
    | ~ m1_subset_1(sK11(sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_393 ),
    inference(resolution,[],[f3195,f134])).

fof(f3195,plain,
    ( ~ r2_hidden(sK11(sK1),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_393 ),
    inference(avatar_component_clause,[],[f3194])).

fof(f3459,plain,
    ( ~ spl16_405
    | spl16_29
    | spl16_393 ),
    inference(avatar_split_clause,[],[f3451,f3194,f264,f3457])).

fof(f3457,plain,
    ( spl16_405
  <=> ~ m1_subset_1(sK11(sK1),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_405])])).

fof(f3451,plain,
    ( ~ m1_subset_1(sK11(sK1),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_29
    | ~ spl16_393 ),
    inference(unit_resulting_resolution,[],[f297,f3195,f123])).

fof(f3422,plain,
    ( ~ spl16_403
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f3415,f264,f173,f166,f159,f152,f145,f3420])).

fof(f3415,plain,
    ( ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(forward_demodulation,[],[f3408,f426])).

fof(f3408,plain,
    ( ~ r2_hidden(sK13(sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK0,u1_struct_0(sK0)),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f146,f160,f174,f167,f153,f297,f370,f1933])).

fof(f1933,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK13(X1,X0,u1_struct_0(X0)),X2)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,a_2_0_yellow_0(X0,u1_struct_0(X0)))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | r2_yellow_0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f1928])).

fof(f1928,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,a_2_0_yellow_0(X0,u1_struct_0(X0)))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ r2_hidden(sK13(X1,X0,u1_struct_0(X0)),X2)
      | r2_yellow_0(X0,X2)
      | ~ r2_hidden(X1,a_2_0_yellow_0(X0,u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f1212,f128])).

fof(f1212,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK13(X2,X3,u1_struct_0(X3)),u1_struct_0(X3))
      | ~ v3_lattice3(X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_orders_2(X3)
      | ~ r2_hidden(X2,a_2_0_yellow_0(X3,u1_struct_0(X3)))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ r2_hidden(sK13(X2,X3,u1_struct_0(X3)),X4)
      | r2_yellow_0(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f1207])).

fof(f1207,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,a_2_0_yellow_0(X3,u1_struct_0(X3)))
      | ~ v3_lattice3(X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(sK13(X2,X3,u1_struct_0(X3)),u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ r2_hidden(sK13(X2,X3,u1_struct_0(X3)),X4)
      | r2_yellow_0(X3,X4)
      | ~ m1_subset_1(sK13(X2,X3,u1_struct_0(X3)),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f799,f612])).

fof(f3321,plain,
    ( ~ spl16_401
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_181 ),
    inference(avatar_split_clause,[],[f3278,f1811,f264,f173,f166,f159,f152,f3319])).

fof(f3319,plain,
    ( spl16_401
  <=> ~ r2_hidden(sK4(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_401])])).

fof(f1811,plain,
    ( spl16_181
  <=> ~ r1_lattice3(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_181])])).

fof(f3278,plain,
    ( ~ r2_hidden(sK4(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_181 ),
    inference(unit_resulting_resolution,[],[f160,f1812,f153,f174,f167,f297,f1859])).

fof(f1812,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_181 ),
    inference(avatar_component_clause,[],[f1811])).

fof(f3314,plain,
    ( ~ spl16_399
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_69 ),
    inference(avatar_split_clause,[],[f3279,f830,f264,f173,f166,f159,f152,f3312])).

fof(f3279,plain,
    ( ~ r2_hidden(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_69 ),
    inference(unit_resulting_resolution,[],[f160,f831,f153,f174,f167,f297,f1859])).

fof(f3307,plain,
    ( ~ spl16_397
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_179 ),
    inference(avatar_split_clause,[],[f3280,f1804,f264,f173,f166,f159,f152,f3305])).

fof(f3305,plain,
    ( spl16_397
  <=> ~ r2_hidden(sK10(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_397])])).

fof(f3280,plain,
    ( ~ r2_hidden(sK10(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_179 ),
    inference(unit_resulting_resolution,[],[f160,f1805,f153,f174,f167,f297,f1859])).

fof(f3300,plain,
    ( ~ spl16_395
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_137 ),
    inference(avatar_split_clause,[],[f3281,f1495,f264,f173,f166,f159,f152,f3298])).

fof(f3298,plain,
    ( spl16_395
  <=> ~ r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_395])])).

fof(f1495,plain,
    ( spl16_137
  <=> ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_137])])).

fof(f3281,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_137 ),
    inference(unit_resulting_resolution,[],[f160,f1496,f153,f174,f167,f297,f1859])).

fof(f1496,plain,
    ( ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_137 ),
    inference(avatar_component_clause,[],[f1495])).

fof(f3196,plain,
    ( ~ spl16_393
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f3175,f264,f173,f166,f159,f152,f145,f3194])).

fof(f3175,plain,
    ( ~ r2_hidden(sK11(sK1),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f174,f160,f370,f153,f146,f167,f1759])).

fof(f3173,plain,
    ( ~ spl16_9
    | ~ spl16_5
    | spl16_390
    | ~ spl16_194 ),
    inference(avatar_split_clause,[],[f3169,f2100,f3171,f149,f163])).

fof(f3171,plain,
    ( spl16_390
  <=> ! [X1,X0] :
        ( ~ l1_orders_2(X0)
        | ~ r1_lattice3(sK0,u1_struct_0(X0),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X0,X1))))
        | r2_yellow_0(sK0,u1_struct_0(X0))
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X0,X1))),u1_struct_0(sK0))
        | ~ v3_lattice3(X0)
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_390])])).

fof(f2100,plain,
    ( spl16_194
  <=> ! [X31,X30] :
        ( ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31))),u1_struct_0(sK0))
        | ~ l1_orders_2(X30)
        | v1_xboole_0(u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v5_orders_2(X30)
        | ~ v3_lattice3(X30)
        | ~ m1_subset_1(sK7(sK0,u1_struct_0(X30),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31)))),u1_struct_0(sK0))
        | r2_yellow_0(sK0,u1_struct_0(X30))
        | ~ r1_lattice3(sK0,u1_struct_0(X30),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_194])])).

fof(f3169,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | v1_xboole_0(u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X0,X1))),u1_struct_0(sK0))
        | r2_yellow_0(sK0,u1_struct_0(X0))
        | ~ r1_lattice3(sK0,u1_struct_0(X0),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X0,X1))))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl16_194 ),
    inference(duplicate_literal_removal,[],[f3167])).

fof(f3167,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(X0)
        | v1_xboole_0(u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v5_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X0,X1))),u1_struct_0(sK0))
        | r2_yellow_0(sK0,u1_struct_0(X0))
        | ~ r1_lattice3(sK0,u1_struct_0(X0),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X0,X1))))
        | r2_yellow_0(sK0,u1_struct_0(X0))
        | ~ r1_lattice3(sK0,u1_struct_0(X0),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X0,X1))))
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X0,X1))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl16_194 ),
    inference(resolution,[],[f2101,f111])).

fof(f2101,plain,
    ( ! [X30,X31] :
        ( ~ m1_subset_1(sK7(sK0,u1_struct_0(X30),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31)))),u1_struct_0(sK0))
        | ~ l1_orders_2(X30)
        | v1_xboole_0(u1_struct_0(X30))
        | v2_struct_0(X30)
        | ~ v5_orders_2(X30)
        | ~ v3_lattice3(X30)
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31))),u1_struct_0(sK0))
        | r2_yellow_0(sK0,u1_struct_0(X30))
        | ~ r1_lattice3(sK0,u1_struct_0(X30),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31)))) )
    | ~ spl16_194 ),
    inference(avatar_component_clause,[],[f2100])).

fof(f3159,plain,
    ( ~ spl16_389
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f3119,f1427,f1353,f264,f173,f166,f159,f152,f145,f3157])).

fof(f3157,plain,
    ( spl16_389
  <=> ~ r2_hidden(sK13(sK8(sK0,u1_struct_0(sK0)),sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_389])])).

fof(f3119,plain,
    ( ~ r2_hidden(sK13(sK8(sK0,u1_struct_0(sK0)),sK0,sK1),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f174,f160,f167,f153,f146,f2415,f1123])).

fof(f3094,plain,
    ( ~ spl16_5
    | spl16_386
    | ~ spl16_106 ),
    inference(avatar_split_clause,[],[f3090,f1200,f3092,f149])).

fof(f3092,plain,
    ( spl16_386
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X0)),u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0)))
        | ~ m1_subset_1(sK5(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0))),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_386])])).

fof(f3090,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X0)),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0))),X0)
        | ~ m1_subset_1(sK5(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0))),u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl16_106 ),
    inference(duplicate_literal_removal,[],[f3085])).

fof(f3085,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X0)),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0))),X0)
        | ~ m1_subset_1(sK5(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0))),u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK11(a_2_0_yellow_0(sK0,X0)))
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X0)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl16_106 ),
    inference(resolution,[],[f1201,f103])).

fof(f3074,plain,
    ( ~ spl16_7
    | ~ spl16_5
    | ~ spl16_89
    | ~ spl16_9
    | spl16_10
    | spl16_384
    | ~ spl16_154 ),
    inference(avatar_split_clause,[],[f3066,f1600,f3072,f170,f163,f987,f149,f156])).

fof(f3072,plain,
    ( spl16_384
  <=> ! [X2] :
        ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,X2))
        | ~ r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_384])])).

fof(f3066,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,X2))
        | v2_struct_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),X2)
        | ~ v3_lattice3(sK0) )
    | ~ spl16_154 ),
    inference(resolution,[],[f1601,f1128])).

fof(f3070,plain,
    ( ~ spl16_5
    | ~ spl16_89
    | spl16_382
    | ~ spl16_154 ),
    inference(avatar_split_clause,[],[f3065,f1600,f3068,f987,f149])).

fof(f3068,plain,
    ( spl16_382
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(X0,X1))
        | ~ r2_lattice3(sK0,u1_struct_0(X0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
        | ~ v3_lattice3(X0)
        | ~ l1_orders_2(X0)
        | v1_xboole_0(u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v5_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_382])])).

fof(f3065,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(X0,X1))
        | ~ v5_orders_2(X0)
        | v2_struct_0(X0)
        | v1_xboole_0(u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v3_lattice3(X0)
        | ~ m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_lattice3(sK0,u1_struct_0(X0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) )
    | ~ spl16_154 ),
    inference(resolution,[],[f1601,f852])).

fof(f852,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_lattice3(X5,a_2_0_yellow_0(X4,X6),X7)
      | ~ v5_orders_2(X4)
      | v2_struct_0(X4)
      | v1_xboole_0(u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v3_lattice3(X4)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ r2_lattice3(X5,u1_struct_0(X4),X7) ) ),
    inference(duplicate_literal_removal,[],[f851])).

fof(f851,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v3_lattice3(X4)
      | ~ v5_orders_2(X4)
      | v2_struct_0(X4)
      | v1_xboole_0(u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r2_lattice3(X5,a_2_0_yellow_0(X4,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ r2_lattice3(X5,u1_struct_0(X4),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | r2_lattice3(X5,a_2_0_yellow_0(X4,X6),X7) ) ),
    inference(resolution,[],[f589,f457])).

fof(f589,plain,(
    ! [X17,X15,X18,X16] :
      ( r2_hidden(sK6(X16,a_2_0_yellow_0(X15,X17),X18),u1_struct_0(X15))
      | ~ v3_lattice3(X15)
      | ~ v5_orders_2(X15)
      | v2_struct_0(X15)
      | v1_xboole_0(u1_struct_0(X15))
      | ~ l1_orders_2(X15)
      | r2_lattice3(X16,a_2_0_yellow_0(X15,X17),X18)
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ l1_orders_2(X16) ) ),
    inference(resolution,[],[f443,f106])).

fof(f3054,plain,
    ( spl16_380
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_88
    | ~ spl16_174 ),
    inference(avatar_split_clause,[],[f3026,f1744,f990,f159,f152,f3052])).

fof(f3052,plain,
    ( spl16_380
  <=> r1_orders_2(sK0,sK4(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_380])])).

fof(f990,plain,
    ( spl16_88
  <=> m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_88])])).

fof(f1744,plain,
    ( spl16_174
  <=> r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_174])])).

fof(f3026,plain,
    ( r1_orders_2(sK0,sK4(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_88
    | ~ spl16_174 ),
    inference(unit_resulting_resolution,[],[f153,f160,f991,f1745,f96])).

fof(f1745,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_174 ),
    inference(avatar_component_clause,[],[f1744])).

fof(f991,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_88 ),
    inference(avatar_component_clause,[],[f990])).

fof(f3047,plain,
    ( spl16_378
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_88
    | ~ spl16_174 ),
    inference(avatar_split_clause,[],[f3029,f1744,f990,f166,f159,f152,f3045])).

fof(f3045,plain,
    ( spl16_378
  <=> r1_orders_2(sK0,sK10(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_378])])).

fof(f3029,plain,
    ( r1_orders_2(sK0,sK10(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_88
    | ~ spl16_174 ),
    inference(unit_resulting_resolution,[],[f167,f153,f682,f991,f1745,f116])).

fof(f3040,plain,
    ( ~ spl16_377
    | ~ spl16_4
    | ~ spl16_88
    | spl16_149
    | ~ spl16_174 ),
    inference(avatar_split_clause,[],[f3030,f1744,f1541,f990,f152,f3038])).

fof(f3038,plain,
    ( spl16_377
  <=> ~ r2_hidden(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_377])])).

fof(f1541,plain,
    ( spl16_149
  <=> ~ r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_149])])).

fof(f3030,plain,
    ( ~ r2_hidden(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_149
    | ~ spl16_174 ),
    inference(unit_resulting_resolution,[],[f153,f1542,f991,f1745,f457])).

fof(f1542,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_149 ),
    inference(avatar_component_clause,[],[f1541])).

fof(f3024,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_373 ),
    inference(avatar_contradiction_clause,[],[f3016])).

fof(f3016,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_373 ),
    inference(unit_resulting_resolution,[],[f444,f2998,f122])).

fof(f2998,plain,
    ( ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl16_373 ),
    inference(avatar_component_clause,[],[f2997])).

fof(f2997,plain,
    ( spl16_373
  <=> ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_373])])).

fof(f3023,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_373 ),
    inference(avatar_contradiction_clause,[],[f3014])).

fof(f3014,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_373 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f2998,f272])).

fof(f3022,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_373 ),
    inference(avatar_contradiction_clause,[],[f3008])).

fof(f3008,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_373 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f2998,f429])).

fof(f3021,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_373 ),
    inference(avatar_contradiction_clause,[],[f3003])).

fof(f3003,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_373 ),
    inference(unit_resulting_resolution,[],[f430,f2998])).

fof(f3020,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_373 ),
    inference(avatar_contradiction_clause,[],[f3017])).

fof(f3017,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_373 ),
    inference(resolution,[],[f2998,f430])).

fof(f3002,plain,
    ( ~ spl16_5
    | ~ spl16_373
    | ~ spl16_103
    | spl16_374
    | spl16_99 ),
    inference(avatar_split_clause,[],[f2990,f1178,f3000,f1189,f2997,f149])).

fof(f1189,plain,
    ( spl16_103
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_103])])).

fof(f3000,plain,
    ( spl16_374
  <=> ! [X0] :
        ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),X0)
        | ~ r2_lattice3(sK0,X0,sK11(a_2_0_yellow_0(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_374])])).

fof(f1178,plain,
    ( spl16_99
  <=> ~ r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK11(a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_99])])).

fof(f2990,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),X0)
        | ~ m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK11(a_2_0_yellow_0(sK0,sK1)))
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl16_99 ),
    inference(resolution,[],[f1179,f104])).

fof(f1179,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK11(a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_99 ),
    inference(avatar_component_clause,[],[f1178])).

fof(f2980,plain,
    ( spl16_370
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_88
    | ~ spl16_176 ),
    inference(avatar_split_clause,[],[f2952,f1751,f990,f159,f152,f2978])).

fof(f2978,plain,
    ( spl16_370
  <=> r1_orders_2(sK0,sK4(sK0,a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_370])])).

fof(f1751,plain,
    ( spl16_176
  <=> r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_176])])).

fof(f2952,plain,
    ( r1_orders_2(sK0,sK4(sK0,a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_88
    | ~ spl16_176 ),
    inference(unit_resulting_resolution,[],[f153,f160,f991,f1752,f96])).

fof(f1752,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_176 ),
    inference(avatar_component_clause,[],[f1751])).

fof(f2973,plain,
    ( spl16_368
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_88
    | ~ spl16_176 ),
    inference(avatar_split_clause,[],[f2955,f1751,f990,f166,f159,f152,f2971])).

fof(f2971,plain,
    ( spl16_368
  <=> r1_orders_2(sK0,sK10(sK0,a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_368])])).

fof(f2955,plain,
    ( r1_orders_2(sK0,sK10(sK0,a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_88
    | ~ spl16_176 ),
    inference(unit_resulting_resolution,[],[f167,f153,f682,f991,f1752,f116])).

fof(f2966,plain,
    ( ~ spl16_367
    | ~ spl16_4
    | ~ spl16_88
    | spl16_149
    | ~ spl16_176 ),
    inference(avatar_split_clause,[],[f2956,f1751,f1541,f990,f152,f2964])).

fof(f2964,plain,
    ( spl16_367
  <=> ~ r2_hidden(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_367])])).

fof(f2956,plain,
    ( ~ r2_hidden(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_149
    | ~ spl16_176 ),
    inference(unit_resulting_resolution,[],[f153,f1542,f991,f1752,f457])).

fof(f2949,plain,
    ( spl16_10
    | ~ spl16_7
    | ~ spl16_5
    | ~ spl16_9
    | spl16_364
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f2913,f264,f173,f166,f159,f152,f2947,f163,f149,f156,f170])).

fof(f2947,plain,
    ( spl16_364
  <=> ! [X0] :
        ( ~ r1_lattice3(sK0,a_2_0_yellow_0(sK0,X0),sK11(a_2_0_yellow_0(sK0,X0)))
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X0)),u1_struct_0(sK0))
        | r2_yellow_0(sK0,a_2_0_yellow_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_364])])).

fof(f2913,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,a_2_0_yellow_0(sK0,X0),sK11(a_2_0_yellow_0(sK0,X0)))
        | r2_yellow_0(sK0,a_2_0_yellow_0(sK0,X0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X0)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_lattice3(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(resolution,[],[f1706,f1205])).

fof(f2945,plain,
    ( ~ spl16_363
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2905,f1192,f264,f173,f166,f159,f152,f145,f2943])).

fof(f2943,plain,
    ( spl16_363
  <=> ~ r1_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_363])])).

fof(f2905,plain,
    ( ~ r1_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f167,f153,f146,f430,f431,f1193,f1706,f604])).

fof(f2938,plain,
    ( ~ spl16_357
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2909,f1192,f264,f173,f166,f159,f152,f145,f2921])).

fof(f2921,plain,
    ( spl16_357
  <=> ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_357])])).

fof(f2909,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f430,f431,f1193,f1706,f311])).

fof(f2937,plain,
    ( ~ spl16_361
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_93 ),
    inference(avatar_split_clause,[],[f2910,f1157,f264,f173,f166,f159,f152,f2935])).

fof(f2935,plain,
    ( spl16_361
  <=> ~ r2_hidden(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_361])])).

fof(f1157,plain,
    ( spl16_93
  <=> ~ r2_lattice3(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_93])])).

fof(f2910,plain,
    ( ~ r2_hidden(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f153,f1158,f430,f1706,f457])).

fof(f1158,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_93 ),
    inference(avatar_component_clause,[],[f1157])).

fof(f2930,plain,
    ( ~ spl16_359
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2911,f1818,f264,f173,f166,f159,f152,f2928])).

fof(f2928,plain,
    ( spl16_359
  <=> ~ r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_359])])).

fof(f2911,plain,
    ( ~ r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f1819,f430,f1706,f457])).

fof(f2923,plain,
    ( ~ spl16_357
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f2912,f264,f173,f166,f159,f152,f145,f2921])).

fof(f2912,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f146,f167,f431,f430,f1706,f462])).

fof(f2902,plain,
    ( spl16_354
    | ~ spl16_4
    | ~ spl16_88
    | spl16_149 ),
    inference(avatar_split_clause,[],[f2866,f1541,f990,f152,f2900])).

fof(f2900,plain,
    ( spl16_354
  <=> m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_354])])).

fof(f2866,plain,
    ( m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_149 ),
    inference(unit_resulting_resolution,[],[f153,f991,f1542,f105])).

fof(f2895,plain,
    ( spl16_350
    | ~ spl16_4
    | ~ spl16_88
    | spl16_149 ),
    inference(avatar_split_clause,[],[f2867,f1541,f990,f152,f2884])).

fof(f2884,plain,
    ( spl16_350
  <=> r2_hidden(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_350])])).

fof(f2867,plain,
    ( r2_hidden(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_149 ),
    inference(unit_resulting_resolution,[],[f153,f991,f1542,f106])).

fof(f2894,plain,
    ( ~ spl16_353
    | ~ spl16_4
    | ~ spl16_88
    | spl16_149 ),
    inference(avatar_split_clause,[],[f2868,f1541,f990,f152,f2892])).

fof(f2892,plain,
    ( spl16_353
  <=> ~ r1_orders_2(sK0,sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_353])])).

fof(f2868,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_149 ),
    inference(unit_resulting_resolution,[],[f153,f991,f1542,f107])).

fof(f2887,plain,
    ( ~ spl16_349
    | ~ spl16_4
    | ~ spl16_88
    | spl16_149 ),
    inference(avatar_split_clause,[],[f2869,f1541,f990,f152,f2877])).

fof(f2877,plain,
    ( spl16_349
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_349])])).

fof(f2869,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_149 ),
    inference(unit_resulting_resolution,[],[f153,f991,f1542,f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,sK6(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f106,f121])).

fof(f2886,plain,
    ( spl16_350
    | ~ spl16_4
    | spl16_29
    | ~ spl16_88
    | spl16_149 ),
    inference(avatar_split_clause,[],[f2870,f1541,f990,f264,f152,f2884])).

fof(f2870,plain,
    ( r2_hidden(sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_29
    | ~ spl16_88
    | ~ spl16_149 ),
    inference(unit_resulting_resolution,[],[f153,f297,f991,f1542,f246])).

fof(f2879,plain,
    ( ~ spl16_349
    | ~ spl16_4
    | spl16_29
    | ~ spl16_88
    | spl16_149 ),
    inference(avatar_split_clause,[],[f2871,f1541,f990,f264,f152,f2877])).

fof(f2871,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))))
    | ~ spl16_4
    | ~ spl16_29
    | ~ spl16_88
    | ~ spl16_149 ),
    inference(unit_resulting_resolution,[],[f153,f297,f991,f1542,f410])).

fof(f410,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X1),sK6(X1,X2,X0))
      | ~ l1_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | r2_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f246,f121])).

fof(f2865,plain,
    ( ~ spl16_347
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2825,f1192,f264,f173,f166,f159,f152,f145,f2863])).

fof(f2863,plain,
    ( spl16_347
  <=> ~ r1_lattice3(sK0,u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_347])])).

fof(f2825,plain,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f167,f153,f146,f430,f431,f1193,f1707,f604])).

fof(f2858,plain,
    ( ~ spl16_341
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2830,f1192,f264,f173,f166,f159,f152,f145,f2841])).

fof(f2841,plain,
    ( spl16_341
  <=> ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_341])])).

fof(f2830,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f430,f431,f1193,f1707,f311])).

fof(f2857,plain,
    ( ~ spl16_345
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_93 ),
    inference(avatar_split_clause,[],[f2831,f1157,f264,f173,f166,f159,f152,f2855])).

fof(f2855,plain,
    ( spl16_345
  <=> ~ r2_hidden(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_345])])).

fof(f2831,plain,
    ( ~ r2_hidden(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f153,f1158,f430,f1707,f457])).

fof(f2850,plain,
    ( ~ spl16_343
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2832,f1818,f264,f173,f166,f159,f152,f2848])).

fof(f2848,plain,
    ( spl16_343
  <=> ~ r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_343])])).

fof(f2832,plain,
    ( ~ r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f1819,f430,f1707,f457])).

fof(f2843,plain,
    ( ~ spl16_341
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f2833,f264,f173,f166,f159,f152,f145,f2841])).

fof(f2833,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f146,f167,f431,f430,f1707,f462])).

fof(f2824,plain,
    ( spl16_338
    | ~ spl16_4
    | ~ spl16_88
    | spl16_137 ),
    inference(avatar_split_clause,[],[f2769,f1495,f990,f152,f2822])).

fof(f2822,plain,
    ( spl16_338
  <=> m1_subset_1(sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_338])])).

fof(f2769,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_137 ),
    inference(unit_resulting_resolution,[],[f153,f991,f1496,f101])).

fof(f2817,plain,
    ( spl16_336
    | ~ spl16_4
    | ~ spl16_88
    | spl16_137 ),
    inference(avatar_split_clause,[],[f2770,f1495,f990,f152,f2815])).

fof(f2815,plain,
    ( spl16_336
  <=> r2_hidden(sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_336])])).

fof(f2770,plain,
    ( r2_hidden(sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),sK1)
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_137 ),
    inference(unit_resulting_resolution,[],[f153,f991,f1496,f102])).

fof(f2810,plain,
    ( ~ spl16_335
    | ~ spl16_4
    | ~ spl16_88
    | spl16_137 ),
    inference(avatar_split_clause,[],[f2771,f1495,f990,f152,f2808])).

fof(f2808,plain,
    ( spl16_335
  <=> ~ r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_335])])).

fof(f2771,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_137 ),
    inference(unit_resulting_resolution,[],[f153,f991,f1496,f103])).

fof(f2803,plain,
    ( ~ spl16_333
    | ~ spl16_4
    | ~ spl16_88
    | spl16_137 ),
    inference(avatar_split_clause,[],[f2772,f1495,f990,f152,f2801])).

fof(f2801,plain,
    ( spl16_333
  <=> ~ r2_hidden(sK1,sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_333])])).

fof(f2772,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))))
    | ~ spl16_4
    | ~ spl16_88
    | ~ spl16_137 ),
    inference(unit_resulting_resolution,[],[f153,f991,f1496,f230])).

fof(f2796,plain,
    ( spl16_330
    | ~ spl16_4
    | spl16_29
    | ~ spl16_88
    | spl16_137 ),
    inference(avatar_split_clause,[],[f2773,f1495,f990,f264,f152,f2794])).

fof(f2794,plain,
    ( spl16_330
  <=> r2_hidden(sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_330])])).

fof(f2773,plain,
    ( r2_hidden(sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_29
    | ~ spl16_88
    | ~ spl16_137 ),
    inference(unit_resulting_resolution,[],[f153,f297,f991,f1496,f245])).

fof(f2789,plain,
    ( ~ spl16_329
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_137 ),
    inference(avatar_split_clause,[],[f2774,f1495,f173,f166,f159,f152,f2787])).

fof(f2787,plain,
    ( spl16_329
  <=> ~ r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_329])])).

fof(f2774,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_137 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f1496,f274])).

fof(f2782,plain,
    ( ~ spl16_327
    | ~ spl16_4
    | spl16_29
    | ~ spl16_88
    | spl16_137 ),
    inference(avatar_split_clause,[],[f2775,f1495,f990,f264,f152,f2780])).

fof(f2780,plain,
    ( spl16_327
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_327])])).

fof(f2775,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))))
    | ~ spl16_4
    | ~ spl16_29
    | ~ spl16_88
    | ~ spl16_137 ),
    inference(unit_resulting_resolution,[],[f153,f297,f991,f1496,f409])).

fof(f2766,plain,
    ( ~ spl16_325
    | spl16_29
    | spl16_159 ),
    inference(avatar_split_clause,[],[f2758,f1650,f264,f2764])).

fof(f2764,plain,
    ( spl16_325
  <=> ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_325])])).

fof(f1650,plain,
    ( spl16_159
  <=> ~ r2_hidden(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_159])])).

fof(f2758,plain,
    ( ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_29
    | ~ spl16_159 ),
    inference(unit_resulting_resolution,[],[f297,f1651,f123])).

fof(f1651,plain,
    ( ~ r2_hidden(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_159 ),
    inference(avatar_component_clause,[],[f1650])).

fof(f2756,plain,
    ( spl16_322
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_86
    | ~ spl16_88
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2602,f1192,f990,f983,f264,f173,f166,f159,f152,f145,f2753])).

fof(f2753,plain,
    ( spl16_322
  <=> r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_322])])).

fof(f983,plain,
    ( spl16_86
  <=> r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_86])])).

fof(f2602,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_86
    | ~ spl16_88
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f167,f146,f984,f991,f431,f430,f1193,f307])).

fof(f984,plain,
    ( r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_86 ),
    inference(avatar_component_clause,[],[f983])).

fof(f2755,plain,
    ( spl16_322
    | ~ spl16_4
    | ~ spl16_86
    | ~ spl16_88
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2608,f1192,f1185,f990,f983,f152,f2753])).

fof(f2608,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_86
    | ~ spl16_88
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f984,f991,f1186,f1193,f100])).

fof(f2748,plain,
    ( spl16_300
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2609,f1192,f1171,f264,f173,f166,f159,f152,f2670])).

fof(f2670,plain,
    ( spl16_300
  <=> r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_300])])).

fof(f1171,plain,
    ( spl16_96
  <=> r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_96])])).

fof(f2609,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f430,f431,f1172,f1193,f100])).

fof(f1172,plain,
    ( r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_96 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f2747,plain,
    ( spl16_298
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_96
    | ~ spl16_102
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2610,f1427,f1353,f1192,f1171,f264,f166,f152,f2663])).

fof(f2663,plain,
    ( spl16_298
  <=> r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_298])])).

fof(f2610,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_96
    | ~ spl16_102
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f153,f1428,f2031,f1172,f1193,f100])).

fof(f2746,plain,
    ( spl16_320
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2611,f1192,f1171,f159,f152,f2743])).

fof(f2743,plain,
    ( spl16_320
  <=> r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK4(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_320])])).

fof(f2611,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f209,f211,f1172,f1193,f104])).

fof(f2745,plain,
    ( spl16_320
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2612,f1192,f1171,f264,f159,f152,f2743])).

fof(f2612,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f209,f699,f1172,f1193,f104])).

fof(f2738,plain,
    ( spl16_318
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2613,f1192,f1171,f166,f159,f152,f2735])).

fof(f2735,plain,
    ( spl16_318
  <=> r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK10(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_318])])).

fof(f2613,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f683,f684,f1172,f1193,f104])).

fof(f2737,plain,
    ( spl16_318
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2614,f1192,f1171,f264,f166,f159,f152,f2735])).

fof(f2614,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f683,f820,f1172,f1193,f104])).

fof(f2730,plain,
    ( spl16_316
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2615,f1192,f1185,f166,f152,f145,f2728])).

fof(f2728,plain,
    ( spl16_316
  <=> m1_subset_1(sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_316])])).

fof(f2615,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))),u1_struct_0(sK0))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f1186,f1193,f111])).

fof(f2723,plain,
    ( spl16_314
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2616,f1192,f1185,f166,f152,f145,f2721])).

fof(f2721,plain,
    ( spl16_314
  <=> r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_314])])).

fof(f2616,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f1186,f1193,f112])).

fof(f2716,plain,
    ( ~ spl16_313
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2617,f1192,f1185,f166,f152,f145,f2714])).

fof(f2714,plain,
    ( spl16_313
  <=> ~ r1_orders_2(sK0,sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_313])])).

fof(f2617,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f1186,f1193,f113])).

fof(f2709,plain,
    ( spl16_310
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2618,f1192,f1185,f173,f166,f159,f152,f2707])).

fof(f2707,plain,
    ( spl16_310
  <=> r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_310])])).

fof(f2618,plain,
    ( r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f1186,f1193,f134])).

fof(f2702,plain,
    ( spl16_298
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_96
    | ~ spl16_102
    | ~ spl16_110 ),
    inference(avatar_split_clause,[],[f2619,f1353,f1192,f1171,f166,f152,f2663])).

fof(f2619,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_96
    | ~ spl16_102
    | ~ spl16_110 ),
    inference(unit_resulting_resolution,[],[f167,f153,f1354,f1172,f1193,f279])).

fof(f2701,plain,
    ( ~ spl16_309
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2620,f1192,f1185,f173,f166,f159,f152,f2699])).

fof(f2699,plain,
    ( spl16_309
  <=> ~ r2_hidden(a_2_0_yellow_0(sK0,sK1),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_309])])).

fof(f2620,plain,
    ( ~ r2_hidden(a_2_0_yellow_0(sK0,sK1),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f174,f167,f160,f1186,f1193,f292])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(a_2_0_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(resolution,[],[f134,f121])).

fof(f2694,plain,
    ( spl16_306
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2621,f1192,f1185,f264,f166,f152,f145,f2692])).

fof(f2692,plain,
    ( spl16_306
  <=> r2_hidden(sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_306])])).

fof(f2621,plain,
    ( r2_hidden(sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))),u1_struct_0(sK0))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f297,f1186,f1193,f305])).

fof(f2687,plain,
    ( ~ spl16_305
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2622,f1192,f1185,f264,f166,f152,f145,f2685])).

fof(f2685,plain,
    ( spl16_305
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_305])])).

fof(f2622,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f153,f167,f146,f297,f1186,f1193,f445])).

fof(f2680,plain,
    ( ~ spl16_303
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2623,f1192,f1185,f264,f166,f152,f145,f2678])).

fof(f2678,plain,
    ( spl16_303
  <=> ~ r2_lattice3(sK0,u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_303])])).

fof(f2623,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f167,f153,f297,f146,f1186,f1193,f605])).

fof(f2673,plain,
    ( spl16_300
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2625,f1192,f1171,f264,f173,f166,f159,f152,f2670])).

fof(f2625,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f1172,f1193,f639])).

fof(f2672,plain,
    ( spl16_300
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2627,f1192,f1171,f264,f173,f166,f159,f152,f2670])).

fof(f2627,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f1172,f1193,f773])).

fof(f2665,plain,
    ( spl16_298
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_96
    | ~ spl16_102
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2628,f1427,f1353,f1192,f1171,f264,f166,f152,f2663])).

fof(f2628,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_96
    | ~ spl16_102
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f153,f167,f297,f1354,f1428,f1172,f1193,f1064])).

fof(f2658,plain,
    ( ~ spl16_297
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2629,f1192,f1185,f166,f152,f145,f2656])).

fof(f2656,plain,
    ( spl16_297
  <=> ~ r2_hidden(sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_297])])).

fof(f2629,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f1186,f1193,f1090])).

fof(f2651,plain,
    ( spl16_294
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2630,f1192,f1171,f173,f166,f159,f152,f2649])).

fof(f2649,plain,
    ( spl16_294
  <=> r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_294])])).

fof(f2630,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_96
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f1172,f1193,f1128])).

fof(f2644,plain,
    ( ~ spl16_293
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2631,f1192,f1185,f173,f166,f159,f152,f145,f2642])).

fof(f2642,plain,
    ( spl16_293
  <=> ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_293])])).

fof(f2631,plain,
    ( ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_100
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f174,f160,f153,f167,f146,f1186,f1193,f1205])).

fof(f2601,plain,
    ( ~ spl16_5
    | ~ spl16_103
    | spl16_290
    | ~ spl16_100 ),
    inference(avatar_split_clause,[],[f2596,f1185,f2599,f1189,f149])).

fof(f2599,plain,
    ( spl16_290
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_290])])).

fof(f2596,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),X0)
        | ~ m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl16_100 ),
    inference(resolution,[],[f1186,f100])).

fof(f2586,plain,
    ( ~ spl16_289
    | spl16_29
    | spl16_95 ),
    inference(avatar_split_clause,[],[f2579,f1164,f264,f2584])).

fof(f2584,plain,
    ( spl16_289
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_289])])).

fof(f1164,plain,
    ( spl16_95
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_95])])).

fof(f2579,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_29
    | ~ spl16_95 ),
    inference(unit_resulting_resolution,[],[f297,f1165,f123])).

fof(f1165,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_95 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f2577,plain,
    ( spl16_280
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2492,f1818,f264,f173,f166,f159,f152,f2550])).

fof(f2550,plain,
    ( spl16_280
  <=> m1_subset_1(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_280])])).

fof(f2492,plain,
    ( m1_subset_1(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f160,f153,f174,f167,f430,f1819,f401])).

fof(f2576,plain,
    ( spl16_286
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2493,f1818,f264,f173,f166,f159,f152,f2574])).

fof(f2574,plain,
    ( spl16_286
  <=> r1_lattice3(sK0,sK1,sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_286])])).

fof(f2493,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f160,f153,f174,f167,f430,f1819,f407])).

fof(f2569,plain,
    ( spl16_272
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2494,f1818,f264,f173,f166,f159,f152,f2522])).

fof(f2522,plain,
    ( spl16_272
  <=> r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_272])])).

fof(f2494,plain,
    ( r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f167,f160,f153,f174,f297,f430,f1819,f589])).

fof(f2568,plain,
    ( ~ spl16_271
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2495,f1818,f264,f173,f166,f159,f152,f2515])).

fof(f2515,plain,
    ( spl16_271
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_271])])).

fof(f2495,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f174,f167,f153,f160,f297,f430,f1819,f738])).

fof(f738,plain,(
    ! [X17,X15,X18,X16] :
      ( ~ r2_hidden(u1_struct_0(X15),sK6(X16,a_2_0_yellow_0(X15,X17),X18))
      | ~ v5_orders_2(X15)
      | v2_struct_0(X15)
      | v1_xboole_0(u1_struct_0(X15))
      | ~ v3_lattice3(X15)
      | ~ l1_orders_2(X15)
      | r2_lattice3(X16,a_2_0_yellow_0(X15,X17),X18)
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ l1_orders_2(X16) ) ),
    inference(resolution,[],[f598,f106])).

fof(f598,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(u1_struct_0(X1),X0)
      | ~ l1_orders_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f597])).

fof(f597,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X1),X0)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f441,f129])).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X0),sK13(X1,X0,X2))
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ r2_hidden(X1,a_2_0_yellow_0(X0,X2))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f270,f121])).

fof(f2567,plain,
    ( spl16_284
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_86
    | ~ spl16_88
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2496,f1818,f990,f983,f264,f173,f166,f159,f152,f2565])).

fof(f2565,plain,
    ( spl16_284
  <=> r1_orders_2(sK0,sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_284])])).

fof(f2496,plain,
    ( r1_orders_2(sK0,sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_86
    | ~ spl16_88
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f153,f160,f174,f167,f984,f991,f430,f1819,f776])).

fof(f2560,plain,
    ( ~ spl16_283
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2498,f1818,f264,f173,f166,f159,f152,f145,f2557])).

fof(f2557,plain,
    ( spl16_283
  <=> ~ r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_283])])).

fof(f2498,plain,
    ( ~ r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f153,f167,f174,f160,f146,f430,f1819,f1299])).

fof(f2559,plain,
    ( ~ spl16_283
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2499,f1818,f264,f173,f166,f159,f152,f145,f2557])).

fof(f2499,plain,
    ( ~ r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f167,f174,f160,f146,f430,f1819,f1298])).

fof(f1298,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK6(X4,a_2_0_yellow_0(X4,X5),X6),X5)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,X5)
      | ~ l1_orders_2(X4)
      | ~ v3_lattice3(X4)
      | v2_struct_0(X4)
      | r2_lattice3(X4,a_2_0_yellow_0(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f1296])).

fof(f1296,plain,(
    ! [X6,X4,X5] :
      ( ~ v5_orders_2(X4)
      | ~ r2_hidden(sK6(X4,a_2_0_yellow_0(X4,X5),X6),X5)
      | r2_yellow_0(X4,X5)
      | ~ l1_orders_2(X4)
      | ~ v3_lattice3(X4)
      | v2_struct_0(X4)
      | r2_lattice3(X4,a_2_0_yellow_0(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r2_lattice3(X4,a_2_0_yellow_0(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f730,f105])).

fof(f2552,plain,
    ( spl16_280
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2501,f1818,f264,f173,f166,f159,f152,f2550])).

fof(f2501,plain,
    ( m1_subset_1(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f430,f1819,f105])).

fof(f2545,plain,
    ( spl16_278
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2502,f1818,f264,f173,f166,f159,f152,f2543])).

fof(f2543,plain,
    ( spl16_278
  <=> r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_278])])).

fof(f2502,plain,
    ( r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f430,f1819,f106])).

fof(f2538,plain,
    ( ~ spl16_277
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2503,f1818,f264,f173,f166,f159,f152,f2536])).

fof(f2536,plain,
    ( spl16_277
  <=> ~ r1_orders_2(sK0,sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK11(a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_277])])).

fof(f2503,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),sK11(a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f430,f1819,f107])).

fof(f2531,plain,
    ( ~ spl16_275
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2504,f1818,f264,f173,f166,f159,f152,f2529])).

fof(f2529,plain,
    ( spl16_275
  <=> ~ r2_hidden(a_2_0_yellow_0(sK0,sK1),sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_275])])).

fof(f2504,plain,
    ( ~ r2_hidden(a_2_0_yellow_0(sK0,sK1),sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f430,f1819,f232])).

fof(f2524,plain,
    ( spl16_272
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2505,f1818,f264,f173,f166,f159,f152,f2522])).

fof(f2505,plain,
    ( r2_hidden(sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f297,f430,f1819,f246])).

fof(f2517,plain,
    ( ~ spl16_271
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_183 ),
    inference(avatar_split_clause,[],[f2506,f1818,f264,f173,f166,f159,f152,f2515])).

fof(f2506,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_183 ),
    inference(unit_resulting_resolution,[],[f153,f297,f430,f1819,f410])).

fof(f2491,plain,
    ( ~ spl16_5
    | ~ spl16_125
    | spl16_268
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2427,f1427,f1353,f264,f166,f152,f2489,f1424,f149])).

fof(f1424,plain,
    ( spl16_125
  <=> ~ m1_subset_1(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_125])])).

fof(f2489,plain,
    ( spl16_268
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X1,X2)
        | r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_268])])).

fof(f2427,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),X1)
        | ~ m1_subset_1(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(resolution,[],[f2031,f100])).

fof(f2487,plain,
    ( ~ spl16_125
    | spl16_266
    | ~ spl16_9
    | ~ spl16_5
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2426,f1427,f1353,f264,f166,f152,f149,f163,f2485,f1424])).

fof(f2485,plain,
    ( spl16_266
  <=> ! [X0] :
        ( ~ r2_hidden(sK8(sK0,u1_struct_0(sK0)),X0)
        | r2_yellow_0(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_266])])).

fof(f2426,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r2_hidden(sK8(sK0,u1_struct_0(sK0)),X0)
        | r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(resolution,[],[f2031,f612])).

fof(f2483,plain,
    ( spl16_264
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2412,f1427,f1353,f264,f166,f152,f145,f2481])).

fof(f2481,plain,
    ( spl16_264
  <=> m1_subset_1(sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_264])])).

fof(f2412,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f1428,f2031,f111])).

fof(f2476,plain,
    ( spl16_262
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2413,f1427,f1353,f264,f166,f152,f145,f2474])).

fof(f2474,plain,
    ( spl16_262
  <=> r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_262])])).

fof(f2413,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f1428,f2031,f112])).

fof(f2469,plain,
    ( ~ spl16_261
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2414,f1427,f1353,f264,f166,f152,f145,f2467])).

fof(f2467,plain,
    ( spl16_261
  <=> ~ r1_orders_2(sK0,sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_261])])).

fof(f2414,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f1428,f2031,f113])).

fof(f2462,plain,
    ( spl16_258
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2417,f1427,f1353,f264,f166,f152,f145,f2460])).

fof(f2460,plain,
    ( spl16_258
  <=> r2_hidden(sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_258])])).

fof(f2417,plain,
    ( r2_hidden(sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f146,f153,f167,f297,f1428,f2031,f305])).

fof(f2455,plain,
    ( ~ spl16_257
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2418,f1427,f1353,f264,f166,f152,f145,f2453])).

fof(f2453,plain,
    ( spl16_257
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_257])])).

fof(f2418,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f153,f146,f167,f297,f1428,f2031,f445])).

fof(f2448,plain,
    ( ~ spl16_255
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2419,f1427,f1353,f264,f166,f152,f145,f2446])).

fof(f2446,plain,
    ( spl16_255
  <=> ~ r2_lattice3(sK0,u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_255])])).

fof(f2419,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f153,f167,f146,f297,f1428,f2031,f605])).

fof(f2441,plain,
    ( ~ spl16_253
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2423,f1427,f1353,f264,f166,f152,f145,f2439])).

fof(f2439,plain,
    ( spl16_253
  <=> ~ r2_hidden(sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_253])])).

fof(f2423,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK8(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f146,f167,f153,f1428,f2031,f1090])).

fof(f2434,plain,
    ( ~ spl16_251
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2424,f1427,f1353,f264,f173,f166,f159,f152,f145,f2432])).

fof(f2432,plain,
    ( spl16_251
  <=> ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_251])])).

fof(f2424,plain,
    ( ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f174,f160,f153,f146,f167,f1428,f2031,f1205])).

fof(f2403,plain,
    ( spl16_248
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_172 ),
    inference(avatar_split_clause,[],[f2385,f1737,f159,f152,f2401])).

fof(f2401,plain,
    ( spl16_248
  <=> r1_orders_2(sK0,sK4(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK11(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_248])])).

fof(f1737,plain,
    ( spl16_172
  <=> r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK11(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_172])])).

fof(f2385,plain,
    ( r1_orders_2(sK0,sK4(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK11(u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_172 ),
    inference(unit_resulting_resolution,[],[f153,f160,f120,f1738,f96])).

fof(f1738,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK11(u1_struct_0(sK0)))
    | ~ spl16_172 ),
    inference(avatar_component_clause,[],[f1737])).

fof(f2396,plain,
    ( spl16_246
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_172 ),
    inference(avatar_split_clause,[],[f2387,f1737,f166,f159,f152,f2394])).

fof(f2394,plain,
    ( spl16_246
  <=> r1_orders_2(sK0,sK10(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK11(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_246])])).

fof(f2387,plain,
    ( r1_orders_2(sK0,sK10(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK11(u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_172 ),
    inference(unit_resulting_resolution,[],[f167,f153,f682,f120,f1738,f116])).

fof(f2372,plain,
    ( ~ spl16_245
    | spl16_29
    | spl16_171 ),
    inference(avatar_split_clause,[],[f2365,f1699,f264,f2370])).

fof(f2370,plain,
    ( spl16_245
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_245])])).

fof(f1699,plain,
    ( spl16_171
  <=> ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_171])])).

fof(f2365,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_29
    | ~ spl16_171 ),
    inference(unit_resulting_resolution,[],[f297,f1700,f123])).

fof(f1700,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_171 ),
    inference(avatar_component_clause,[],[f1699])).

fof(f2364,plain,
    ( ~ spl16_243
    | spl16_29
    | spl16_153 ),
    inference(avatar_split_clause,[],[f2356,f1596,f264,f2362])).

fof(f2362,plain,
    ( spl16_243
  <=> ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_243])])).

fof(f1596,plain,
    ( spl16_153
  <=> ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_153])])).

fof(f2356,plain,
    ( ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_29
    | ~ spl16_153 ),
    inference(unit_resulting_resolution,[],[f297,f1597,f123])).

fof(f1597,plain,
    ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_153 ),
    inference(avatar_component_clause,[],[f1596])).

fof(f2348,plain,
    ( spl16_240
    | ~ spl16_4
    | ~ spl16_6
    | spl16_181 ),
    inference(avatar_split_clause,[],[f2293,f1811,f159,f152,f2346])).

fof(f2346,plain,
    ( spl16_240
  <=> m1_subset_1(sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_240])])).

fof(f2293,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_181 ),
    inference(unit_resulting_resolution,[],[f153,f209,f1812,f101])).

fof(f2341,plain,
    ( spl16_238
    | ~ spl16_4
    | ~ spl16_6
    | spl16_181 ),
    inference(avatar_split_clause,[],[f2294,f1811,f159,f152,f2339])).

fof(f2339,plain,
    ( spl16_238
  <=> r2_hidden(sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_238])])).

fof(f2294,plain,
    ( r2_hidden(sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_181 ),
    inference(unit_resulting_resolution,[],[f153,f209,f1812,f102])).

fof(f2334,plain,
    ( ~ spl16_237
    | ~ spl16_4
    | ~ spl16_6
    | spl16_181 ),
    inference(avatar_split_clause,[],[f2295,f1811,f159,f152,f2332])).

fof(f2332,plain,
    ( spl16_237
  <=> ~ r1_orders_2(sK0,sK4(sK0,a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_237])])).

fof(f2295,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_181 ),
    inference(unit_resulting_resolution,[],[f153,f209,f1812,f103])).

fof(f2327,plain,
    ( ~ spl16_235
    | ~ spl16_4
    | ~ spl16_6
    | spl16_181 ),
    inference(avatar_split_clause,[],[f2296,f1811,f159,f152,f2325])).

fof(f2325,plain,
    ( spl16_235
  <=> ~ r2_hidden(sK1,sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_235])])).

fof(f2296,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_181 ),
    inference(unit_resulting_resolution,[],[f153,f209,f1812,f230])).

fof(f2320,plain,
    ( spl16_232
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | spl16_181 ),
    inference(avatar_split_clause,[],[f2297,f1811,f264,f159,f152,f2318])).

fof(f2318,plain,
    ( spl16_232
  <=> r2_hidden(sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_232])])).

fof(f2297,plain,
    ( r2_hidden(sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_181 ),
    inference(unit_resulting_resolution,[],[f153,f297,f209,f1812,f245])).

fof(f2313,plain,
    ( ~ spl16_231
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_181 ),
    inference(avatar_split_clause,[],[f2298,f1811,f173,f166,f159,f152,f2311])).

fof(f2298,plain,
    ( ~ r2_hidden(sK4(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_181 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f1812,f274])).

fof(f2306,plain,
    ( ~ spl16_229
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | spl16_181 ),
    inference(avatar_split_clause,[],[f2299,f1811,f264,f159,f152,f2304])).

fof(f2304,plain,
    ( spl16_229
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_229])])).

fof(f2299,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_181 ),
    inference(unit_resulting_resolution,[],[f153,f297,f209,f1812,f409])).

fof(f2292,plain,
    ( spl16_226
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_179 ),
    inference(avatar_split_clause,[],[f2237,f1804,f166,f159,f152,f2290])).

fof(f2290,plain,
    ( spl16_226
  <=> m1_subset_1(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_226])])).

fof(f2237,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_179 ),
    inference(unit_resulting_resolution,[],[f153,f683,f1805,f101])).

fof(f2285,plain,
    ( spl16_224
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_179 ),
    inference(avatar_split_clause,[],[f2238,f1804,f166,f159,f152,f2283])).

fof(f2238,plain,
    ( r2_hidden(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_179 ),
    inference(unit_resulting_resolution,[],[f153,f683,f1805,f102])).

fof(f2278,plain,
    ( ~ spl16_223
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_179 ),
    inference(avatar_split_clause,[],[f2239,f1804,f166,f159,f152,f2276])).

fof(f2276,plain,
    ( spl16_223
  <=> ~ r1_orders_2(sK0,sK10(sK0,a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_223])])).

fof(f2239,plain,
    ( ~ r1_orders_2(sK0,sK10(sK0,a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_179 ),
    inference(unit_resulting_resolution,[],[f153,f683,f1805,f103])).

fof(f2271,plain,
    ( ~ spl16_221
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_179 ),
    inference(avatar_split_clause,[],[f2240,f1804,f166,f159,f152,f2269])).

fof(f2240,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_179 ),
    inference(unit_resulting_resolution,[],[f153,f683,f1805,f230])).

fof(f2264,plain,
    ( spl16_218
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | spl16_179 ),
    inference(avatar_split_clause,[],[f2241,f1804,f264,f166,f159,f152,f2262])).

fof(f2262,plain,
    ( spl16_218
  <=> r2_hidden(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_218])])).

fof(f2241,plain,
    ( r2_hidden(sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_179 ),
    inference(unit_resulting_resolution,[],[f153,f297,f683,f1805,f245])).

fof(f2257,plain,
    ( ~ spl16_217
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_179 ),
    inference(avatar_split_clause,[],[f2242,f1804,f173,f166,f159,f152,f2255])).

fof(f2242,plain,
    ( ~ r2_hidden(sK10(sK0,a_2_0_yellow_0(sK0,sK1)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_179 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f1805,f274])).

fof(f2250,plain,
    ( ~ spl16_215
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | spl16_179 ),
    inference(avatar_split_clause,[],[f2243,f1804,f264,f166,f159,f152,f2248])).

fof(f2248,plain,
    ( spl16_215
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_215])])).

fof(f2243,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_179 ),
    inference(unit_resulting_resolution,[],[f153,f297,f683,f1805,f409])).

fof(f2236,plain,
    ( spl16_212
    | ~ spl16_4
    | ~ spl16_6
    | spl16_151 ),
    inference(avatar_split_clause,[],[f2200,f1589,f159,f152,f2234])).

fof(f2234,plain,
    ( spl16_212
  <=> m1_subset_1(sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_212])])).

fof(f1589,plain,
    ( spl16_151
  <=> ~ r1_lattice3(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_151])])).

fof(f2200,plain,
    ( m1_subset_1(sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_151 ),
    inference(unit_resulting_resolution,[],[f153,f209,f1590,f101])).

fof(f1590,plain,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_151 ),
    inference(avatar_component_clause,[],[f1589])).

fof(f2229,plain,
    ( spl16_208
    | ~ spl16_4
    | ~ spl16_6
    | spl16_151 ),
    inference(avatar_split_clause,[],[f2201,f1589,f159,f152,f2218])).

fof(f2218,plain,
    ( spl16_208
  <=> r2_hidden(sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_208])])).

fof(f2201,plain,
    ( r2_hidden(sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_151 ),
    inference(unit_resulting_resolution,[],[f153,f209,f1590,f102])).

fof(f2228,plain,
    ( ~ spl16_211
    | ~ spl16_4
    | ~ spl16_6
    | spl16_151 ),
    inference(avatar_split_clause,[],[f2202,f1589,f159,f152,f2226])).

fof(f2226,plain,
    ( spl16_211
  <=> ~ r1_orders_2(sK0,sK4(sK0,u1_struct_0(sK0)),sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_211])])).

fof(f2202,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,u1_struct_0(sK0)),sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_151 ),
    inference(unit_resulting_resolution,[],[f153,f209,f1590,f103])).

fof(f2221,plain,
    ( ~ spl16_207
    | ~ spl16_4
    | ~ spl16_6
    | spl16_151 ),
    inference(avatar_split_clause,[],[f2203,f1589,f159,f152,f2211])).

fof(f2211,plain,
    ( spl16_207
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_207])])).

fof(f2203,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_151 ),
    inference(unit_resulting_resolution,[],[f153,f209,f1590,f230])).

fof(f2220,plain,
    ( spl16_208
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | spl16_151 ),
    inference(avatar_split_clause,[],[f2204,f1589,f264,f159,f152,f2218])).

fof(f2204,plain,
    ( r2_hidden(sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_151 ),
    inference(unit_resulting_resolution,[],[f153,f297,f209,f1590,f245])).

fof(f2213,plain,
    ( ~ spl16_207
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | spl16_151 ),
    inference(avatar_split_clause,[],[f2206,f1589,f264,f159,f152,f2211])).

fof(f2206,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_151 ),
    inference(unit_resulting_resolution,[],[f153,f297,f209,f1590,f409])).

fof(f2197,plain,
    ( spl16_204
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_93 ),
    inference(avatar_split_clause,[],[f2161,f1157,f264,f173,f166,f159,f152,f2195])).

fof(f2195,plain,
    ( spl16_204
  <=> m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_204])])).

fof(f2161,plain,
    ( m1_subset_1(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f153,f430,f1158,f105])).

fof(f2190,plain,
    ( spl16_200
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_93 ),
    inference(avatar_split_clause,[],[f2162,f1157,f264,f173,f166,f159,f152,f2179])).

fof(f2179,plain,
    ( spl16_200
  <=> r2_hidden(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_200])])).

fof(f2162,plain,
    ( r2_hidden(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f153,f430,f1158,f106])).

fof(f2189,plain,
    ( ~ spl16_203
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_93 ),
    inference(avatar_split_clause,[],[f2163,f1157,f264,f173,f166,f159,f152,f2187])).

fof(f2187,plain,
    ( spl16_203
  <=> ~ r1_orders_2(sK0,sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),sK11(a_2_0_yellow_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_203])])).

fof(f2163,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),sK11(a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f153,f430,f1158,f107])).

fof(f2182,plain,
    ( ~ spl16_199
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_93 ),
    inference(avatar_split_clause,[],[f2164,f1157,f264,f173,f166,f159,f152,f2172])).

fof(f2172,plain,
    ( spl16_199
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_199])])).

fof(f2164,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f153,f430,f1158,f232])).

fof(f2181,plain,
    ( spl16_200
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_93 ),
    inference(avatar_split_clause,[],[f2165,f1157,f264,f173,f166,f159,f152,f2179])).

fof(f2165,plain,
    ( r2_hidden(sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f153,f297,f430,f1158,f246])).

fof(f2174,plain,
    ( ~ spl16_199
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | spl16_93 ),
    inference(avatar_split_clause,[],[f2166,f1157,f264,f173,f166,f159,f152,f2172])).

fof(f2166,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f153,f297,f430,f1158,f410])).

fof(f2143,plain,
    ( ~ spl16_197
    | spl16_29
    | spl16_193 ),
    inference(avatar_split_clause,[],[f2136,f2068,f264,f2141])).

fof(f2141,plain,
    ( spl16_197
  <=> ~ m1_subset_1(sK8(sK0,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_197])])).

fof(f2068,plain,
    ( spl16_193
  <=> ~ r2_hidden(sK8(sK0,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_193])])).

fof(f2136,plain,
    ( ~ m1_subset_1(sK8(sK0,u1_struct_0(sK0)),sK1)
    | ~ spl16_29
    | ~ spl16_193 ),
    inference(unit_resulting_resolution,[],[f297,f2069,f123])).

fof(f2069,plain,
    ( ~ r2_hidden(sK8(sK0,u1_struct_0(sK0)),sK1)
    | ~ spl16_193 ),
    inference(avatar_component_clause,[],[f2068])).

fof(f2102,plain,
    ( spl16_10
    | ~ spl16_7
    | ~ spl16_9
    | ~ spl16_5
    | spl16_194
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f2088,f166,f159,f152,f2100,f149,f163,f156,f170])).

fof(f2088,plain,
    ( ! [X30,X31] :
        ( ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31))),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,u1_struct_0(X30),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31))))
        | r2_yellow_0(sK0,u1_struct_0(X30))
        | ~ m1_subset_1(sK7(sK0,u1_struct_0(X30),sK10(sK0,a_2_0_yellow_0(sK0,a_2_0_yellow_0(X30,X31)))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_lattice3(X30)
        | ~ v5_orders_2(X30)
        | v2_struct_0(X30)
        | v1_xboole_0(u1_struct_0(X30))
        | ~ l1_orders_2(X30)
        | ~ v5_orders_2(sK0)
        | ~ v3_lattice3(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(resolution,[],[f1321,f684])).

fof(f1321,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_lattice3(X3,a_2_0_yellow_0(X3,a_2_0_yellow_0(X5,X6)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r1_lattice3(X3,u1_struct_0(X5),X4)
      | r2_yellow_0(X3,u1_struct_0(X5))
      | ~ m1_subset_1(sK7(X3,u1_struct_0(X5),X4),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v3_lattice3(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5)
      | v1_xboole_0(u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ v5_orders_2(X3)
      | ~ v3_lattice3(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f1314])).

fof(f1314,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ v5_orders_2(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ r1_lattice3(X3,u1_struct_0(X5),X4)
      | r2_yellow_0(X3,u1_struct_0(X5))
      | ~ m1_subset_1(sK7(X3,u1_struct_0(X5),X4),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v3_lattice3(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5)
      | v1_xboole_0(u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ r1_lattice3(X3,u1_struct_0(X5),X4)
      | r2_yellow_0(X3,u1_struct_0(X5))
      | ~ r2_lattice3(X3,a_2_0_yellow_0(X3,a_2_0_yellow_0(X5,X6)),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK7(X3,u1_struct_0(X5),X4),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v3_lattice3(X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f873,f604])).

fof(f873,plain,(
    ! [X6,X8,X7,X9] :
      ( r1_lattice3(X6,a_2_0_yellow_0(X8,X9),sK7(X6,u1_struct_0(X8),X7))
      | ~ v5_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_lattice3(X6,u1_struct_0(X8),X7)
      | r2_yellow_0(X6,u1_struct_0(X8))
      | ~ m1_subset_1(sK7(X6,u1_struct_0(X8),X7),u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v3_lattice3(X8)
      | ~ v5_orders_2(X8)
      | v2_struct_0(X8)
      | v1_xboole_0(u1_struct_0(X8))
      | ~ l1_orders_2(X8) ) ),
    inference(duplicate_literal_removal,[],[f871])).

fof(f871,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ r1_lattice3(X6,u1_struct_0(X8),X7)
      | r2_yellow_0(X6,u1_struct_0(X8))
      | ~ m1_subset_1(sK7(X6,u1_struct_0(X8),X7),u1_struct_0(X6))
      | r1_lattice3(X6,a_2_0_yellow_0(X8,X9),sK7(X6,u1_struct_0(X8),X7))
      | ~ v3_lattice3(X8)
      | ~ v5_orders_2(X8)
      | v2_struct_0(X8)
      | v1_xboole_0(u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | r1_lattice3(X6,a_2_0_yellow_0(X8,X9),sK7(X6,u1_struct_0(X8),X7))
      | ~ m1_subset_1(sK7(X6,u1_struct_0(X8),X7),u1_struct_0(X6))
      | ~ l1_orders_2(X6) ) ),
    inference(resolution,[],[f668,f588])).

fof(f668,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X1,X2,sK7(X1,X3,X0)),X3)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r1_lattice3(X1,X3,X0)
      | r2_yellow_0(X1,X3)
      | ~ m1_subset_1(sK7(X1,X3,X0),u1_struct_0(X1))
      | r1_lattice3(X1,X2,sK7(X1,X3,X0)) ) ),
    inference(duplicate_literal_removal,[],[f664])).

fof(f664,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ r2_hidden(sK5(X1,X2,sK7(X1,X3,X0)),X3)
      | ~ r1_lattice3(X1,X3,X0)
      | r2_yellow_0(X1,X3)
      | ~ m1_subset_1(sK7(X1,X3,X0),u1_struct_0(X1))
      | r1_lattice3(X1,X2,sK7(X1,X3,X0))
      | r1_lattice3(X1,X2,sK7(X1,X3,X0))
      | ~ m1_subset_1(sK7(X1,X3,X0),u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f485,f101])).

fof(f485,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(sK5(X3,X6,sK7(X3,X4,X5)),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ r2_hidden(sK5(X3,X6,sK7(X3,X4,X5)),X4)
      | ~ r1_lattice3(X3,X4,X5)
      | r2_yellow_0(X3,X4)
      | ~ m1_subset_1(sK7(X3,X4,X5),u1_struct_0(X3))
      | r1_lattice3(X3,X6,sK7(X3,X4,X5)) ) ),
    inference(duplicate_literal_removal,[],[f480])).

fof(f480,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_lattice3(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ r2_hidden(sK5(X3,X6,sK7(X3,X4,X5)),X4)
      | ~ m1_subset_1(sK5(X3,X6,sK7(X3,X4,X5)),u1_struct_0(X3))
      | r2_yellow_0(X3,X4)
      | ~ m1_subset_1(sK7(X3,X4,X5),u1_struct_0(X3))
      | r1_lattice3(X3,X6,sK7(X3,X4,X5))
      | ~ m1_subset_1(sK7(X3,X4,X5),u1_struct_0(X3))
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f307,f103])).

fof(f2071,plain,
    ( spl16_190
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_118
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2024,f1427,f1406,f1353,f264,f166,f152,f2059])).

fof(f2059,plain,
    ( spl16_190
  <=> r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_190])])).

fof(f1406,plain,
    ( spl16_118
  <=> r2_hidden(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_118])])).

fof(f2024,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_118
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f153,f167,f1407,f1428,f297,f1354,f1428,f1064])).

fof(f1407,plain,
    ( r2_hidden(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl16_118 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f2070,plain,
    ( ~ spl16_193
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2029,f1427,f1353,f264,f166,f152,f145,f2068])).

fof(f2029,plain,
    ( ~ r2_hidden(sK8(sK0,u1_struct_0(sK0)),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f146,f167,f153,f297,f1354,f1428,f1065])).

fof(f1065,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK8(X1,u1_struct_0(X1)),u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ r2_yellow_0(X1,u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(sK8(X1,u1_struct_0(X1)),X2)
      | r2_yellow_0(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f1062])).

fof(f1062,plain,(
    ! [X2,X1] :
      ( ~ r2_yellow_0(X1,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK8(X1,u1_struct_0(X1)),u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ r2_hidden(sK8(X1,u1_struct_0(X1)),X2)
      | r2_yellow_0(X1,X2)
      | ~ m1_subset_1(sK8(X1,u1_struct_0(X1)),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f792,f612])).

fof(f2063,plain,
    ( spl16_188
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2034,f1427,f1353,f173,f166,f159,f152,f2052])).

fof(f2052,plain,
    ( spl16_188
  <=> r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_188])])).

fof(f2034,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_110
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f174,f153,f167,f160,f1354,f1428,f857])).

fof(f857,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,a_2_0_yellow_0(X0,X1),sK8(X0,X1))
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v3_lattice3(X0)
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f853])).

fof(f853,plain,(
    ! [X0,X1] :
      ( ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),sK8(X0,X1))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),sK8(X0,X1))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f634,f401])).

fof(f634,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X0,a_2_0_yellow_0(X0,X1),sK8(X0,X1)),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),sK8(X0,X1))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f631])).

fof(f631,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),sK8(X0,X1))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK6(X0,a_2_0_yellow_0(X0,X1),sK8(X0,X1)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r2_lattice3(X0,a_2_0_yellow_0(X0,X1),sK8(X0,X1))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f407,f287])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,sK6(X0,X2,sK8(X0,X1)))
      | ~ m1_subset_1(sK6(X0,X2,sK8(X0,X1)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r2_lattice3(X0,X2,sK8(X0,X1))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,sK6(X0,X2,sK8(X0,X1)))
      | ~ m1_subset_1(sK6(X0,X2,sK8(X0,X1)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r2_lattice3(X0,X2,sK8(X0,X1))
      | ~ m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f110,f107])).

fof(f110,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK8(X0,X1))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f2062,plain,
    ( spl16_190
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_110
    | ~ spl16_118
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2040,f1427,f1406,f1353,f166,f152,f2059])).

fof(f2040,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_110
    | ~ spl16_118
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f167,f153,f1354,f1407,f1428,f279])).

fof(f2061,plain,
    ( spl16_190
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110
    | ~ spl16_118
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2043,f1427,f1406,f1353,f264,f166,f152,f2059])).

fof(f2043,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110
    | ~ spl16_118
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f153,f167,f297,f1354,f1407,f1428,f1428,f1064])).

fof(f2054,plain,
    ( spl16_188
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_118
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f2044,f1427,f1406,f173,f166,f159,f152,f2052])).

fof(f2044,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_118
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f1407,f1428,f1128])).

fof(f1947,plain,
    ( ~ spl16_187
    | spl16_29
    | spl16_115 ),
    inference(avatar_split_clause,[],[f1940,f1392,f264,f1945])).

fof(f1945,plain,
    ( spl16_187
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_187])])).

fof(f1392,plain,
    ( spl16_115
  <=> ~ r2_hidden(u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_115])])).

fof(f1940,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_29
    | ~ spl16_115 ),
    inference(unit_resulting_resolution,[],[f297,f1393,f123])).

fof(f1393,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_115 ),
    inference(avatar_component_clause,[],[f1392])).

fof(f1845,plain,
    ( spl16_22
    | ~ spl16_73
    | spl16_74
    | ~ spl16_9
    | ~ spl16_5
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1559,f264,f166,f159,f152,f149,f163,f847,f844,f220])).

fof(f1559,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_lattice3(sK0,X1,sK10(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29 ),
    inference(resolution,[],[f820,f605])).

fof(f1844,plain,
    ( spl16_10
    | ~ spl16_7
    | ~ spl16_5
    | ~ spl16_73
    | ~ spl16_9
    | spl16_74
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1790,f264,f166,f159,f152,f847,f163,f844,f149,f156,f170])).

fof(f1790,plain,
    ( ! [X25] :
        ( ~ r1_lattice3(sK0,X25,sK10(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X25)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_lattice3(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29 ),
    inference(resolution,[],[f1205,f820])).

fof(f1843,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | spl16_73 ),
    inference(avatar_contradiction_clause,[],[f1836])).

fof(f1836,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_73 ),
    inference(unit_resulting_resolution,[],[f687,f845,f122])).

fof(f845,plain,
    ( ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl16_73 ),
    inference(avatar_component_clause,[],[f844])).

fof(f1842,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_73 ),
    inference(avatar_contradiction_clause,[],[f1833])).

fof(f1833,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_73 ),
    inference(unit_resulting_resolution,[],[f167,f153,f682,f845,f114])).

fof(f1841,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_73 ),
    inference(avatar_contradiction_clause,[],[f1829])).

fof(f1829,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_73 ),
    inference(unit_resulting_resolution,[],[f683,f845])).

fof(f1840,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_73 ),
    inference(avatar_contradiction_clause,[],[f1837])).

fof(f1837,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_73 ),
    inference(resolution,[],[f845,f683])).

fof(f1824,plain,
    ( spl16_10
    | ~ spl16_7
    | ~ spl16_5
    | ~ spl16_9
    | spl16_184
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f1789,f166,f159,f152,f1822,f163,f149,f156,f170])).

fof(f1789,plain,
    ( ! [X24] :
        ( ~ r1_lattice3(sK0,X24,sK10(sK0,a_2_0_yellow_0(sK0,X24)))
        | r2_yellow_0(sK0,X24)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK10(sK0,a_2_0_yellow_0(sK0,X24)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_lattice3(sK0)
        | v2_struct_0(sK0) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(resolution,[],[f1205,f684])).

fof(f1820,plain,
    ( ~ spl16_183
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1773,f264,f173,f166,f159,f152,f145,f1818])).

fof(f1773,plain,
    ( ~ r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK11(a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f174,f160,f153,f146,f167,f431,f430,f1205])).

fof(f1813,plain,
    ( ~ spl16_181
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11 ),
    inference(avatar_split_clause,[],[f1774,f173,f166,f159,f152,f145,f1811])).

fof(f1774,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11 ),
    inference(unit_resulting_resolution,[],[f174,f160,f153,f146,f167,f209,f211,f1205])).

fof(f1806,plain,
    ( ~ spl16_179
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11 ),
    inference(avatar_split_clause,[],[f1776,f173,f166,f159,f152,f145,f1804])).

fof(f1776,plain,
    ( ~ r1_lattice3(sK0,sK1,sK10(sK0,a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11 ),
    inference(unit_resulting_resolution,[],[f174,f160,f153,f146,f167,f683,f684,f1205])).

fof(f1753,plain,
    ( spl16_176
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1703,f990,f983,f173,f166,f159,f152,f1751])).

fof(f1703,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,sK1),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f984,f991,f1128])).

fof(f1746,plain,
    ( spl16_174
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1704,f990,f962,f173,f166,f159,f152,f1744])).

fof(f962,plain,
    ( spl16_80
  <=> r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_80])])).

fof(f1704,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f963,f991,f1128])).

fof(f963,plain,
    ( r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_80 ),
    inference(avatar_component_clause,[],[f962])).

fof(f1739,plain,
    ( spl16_172
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1708,f264,f173,f166,f159,f152,f1737])).

fof(f1708,plain,
    ( r2_lattice3(sK0,a_2_0_yellow_0(sK0,u1_struct_0(sK0)),sK11(u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f160,f167,f153,f174,f370,f120,f1128])).

fof(f1701,plain,
    ( ~ spl16_171
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1691,f264,f173,f166,f159,f152,f145,f1699])).

fof(f1691,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f146,f153,f431,f430,f1090])).

fof(f1687,plain,
    ( spl16_168
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_69 ),
    inference(avatar_split_clause,[],[f1632,f830,f166,f159,f152,f1685])).

fof(f1632,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_69 ),
    inference(unit_resulting_resolution,[],[f153,f683,f831,f101])).

fof(f1680,plain,
    ( spl16_166
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_69 ),
    inference(avatar_split_clause,[],[f1633,f830,f166,f159,f152,f1678])).

fof(f1633,plain,
    ( r2_hidden(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_69 ),
    inference(unit_resulting_resolution,[],[f153,f683,f831,f102])).

fof(f1673,plain,
    ( ~ spl16_165
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_69 ),
    inference(avatar_split_clause,[],[f1634,f830,f166,f159,f152,f1671])).

fof(f1671,plain,
    ( spl16_165
  <=> ~ r1_orders_2(sK0,sK10(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_165])])).

fof(f1634,plain,
    ( ~ r1_orders_2(sK0,sK10(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_69 ),
    inference(unit_resulting_resolution,[],[f153,f683,f831,f103])).

fof(f1666,plain,
    ( ~ spl16_163
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_69 ),
    inference(avatar_split_clause,[],[f1635,f830,f166,f159,f152,f1664])).

fof(f1635,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_69 ),
    inference(unit_resulting_resolution,[],[f153,f683,f831,f230])).

fof(f1659,plain,
    ( spl16_160
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | spl16_69 ),
    inference(avatar_split_clause,[],[f1636,f830,f264,f166,f159,f152,f1657])).

fof(f1636,plain,
    ( r2_hidden(sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_69 ),
    inference(unit_resulting_resolution,[],[f153,f297,f683,f831,f245])).

fof(f1652,plain,
    ( ~ spl16_159
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_69 ),
    inference(avatar_split_clause,[],[f1637,f830,f173,f166,f159,f152,f1650])).

fof(f1637,plain,
    ( ~ r2_hidden(sK10(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_69 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f831,f274])).

fof(f1645,plain,
    ( ~ spl16_157
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29
    | spl16_69 ),
    inference(avatar_split_clause,[],[f1638,f830,f264,f166,f159,f152,f1643])).

fof(f1638,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK10(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_69 ),
    inference(unit_resulting_resolution,[],[f153,f297,f683,f831,f409])).

fof(f1602,plain,
    ( ~ spl16_5
    | ~ spl16_89
    | ~ spl16_63
    | spl16_154
    | spl16_85 ),
    inference(avatar_split_clause,[],[f1584,f976,f1600,f763,f987,f149])).

fof(f976,plain,
    ( spl16_85
  <=> ~ r1_orders_2(sK0,sK4(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_85])])).

fof(f1584,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),X0)
        | ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
        | ~ m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl16_85 ),
    inference(resolution,[],[f977,f104])).

fof(f977,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_85 ),
    inference(avatar_component_clause,[],[f976])).

fof(f1598,plain,
    ( ~ spl16_153
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | ~ spl16_80
    | spl16_85
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1579,f990,f976,f962,f173,f166,f159,f152,f1596])).

fof(f1579,plain,
    ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_80
    | ~ spl16_85
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f963,f991,f977,f639])).

fof(f1591,plain,
    ( ~ spl16_151
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_80
    | spl16_85
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1582,f990,f976,f962,f159,f152,f1589])).

fof(f1582,plain,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_80
    | ~ spl16_85
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f209,f963,f991,f977,f100])).

fof(f1544,plain,
    ( ~ spl16_149
    | ~ spl16_4
    | ~ spl16_6
    | spl16_61
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1461,f990,f756,f159,f152,f1541])).

fof(f756,plain,
    ( spl16_61
  <=> ~ r1_lattice3(sK0,sK1,sK4(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_61])])).

fof(f1461,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_61
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f160,f209,f757,f991,f248])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK5(X0,X2,sK4(X0,X1)))
      | ~ m1_subset_1(sK5(X0,X2,sK4(X0,X1)),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,sK4(X0,X1))
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK5(X0,X2,sK4(X0,X1)))
      | ~ m1_subset_1(sK5(X0,X2,sK4(X0,X1)),u1_struct_0(X0))
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,sK4(X0,X1))
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f96,f103])).

fof(f757,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_61 ),
    inference(avatar_component_clause,[],[f756])).

fof(f1543,plain,
    ( ~ spl16_149
    | ~ spl16_4
    | ~ spl16_6
    | spl16_23
    | spl16_61
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1462,f990,f756,f217,f159,f152,f1541])).

fof(f217,plain,
    ( spl16_23
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_23])])).

fof(f1462,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_23
    | ~ spl16_61
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f253,f757,f209,f991,f285])).

fof(f253,plain,
    ( ! [X0] : r2_hidden(sK4(sK0,X0),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_23 ),
    inference(unit_resulting_resolution,[],[f209,f218,f123])).

fof(f218,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl16_23 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1536,plain,
    ( spl16_134
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1463,f990,f983,f264,f173,f166,f159,f152,f1488])).

fof(f1488,plain,
    ( spl16_134
  <=> r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_134])])).

fof(f1463,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f430,f431,f984,f991,f100])).

fof(f1535,plain,
    ( spl16_132
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1464,f990,f962,f264,f173,f166,f159,f152,f1481])).

fof(f1481,plain,
    ( spl16_132
  <=> r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_132])])).

fof(f1464,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f430,f431,f963,f991,f100])).

fof(f1534,plain,
    ( spl16_146
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1465,f990,f983,f159,f152,f1532])).

fof(f1532,plain,
    ( spl16_146
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_146])])).

fof(f1465,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK4(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f209,f211,f984,f991,f104])).

fof(f1527,plain,
    ( spl16_142
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1466,f990,f983,f264,f159,f152,f1516])).

fof(f1516,plain,
    ( spl16_142
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK4(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_142])])).

fof(f1466,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f209,f699,f984,f991,f104])).

fof(f1526,plain,
    ( spl16_144
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1467,f990,f983,f166,f159,f152,f1524])).

fof(f1524,plain,
    ( spl16_144
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_144])])).

fof(f1467,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK10(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f683,f684,f984,f991,f104])).

fof(f1519,plain,
    ( spl16_142
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1468,f990,f962,f159,f152,f1516])).

fof(f1468,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f209,f211,f963,f991,f104])).

fof(f1518,plain,
    ( spl16_142
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1469,f990,f962,f264,f159,f152,f1516])).

fof(f1469,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f209,f699,f963,f991,f104])).

fof(f1511,plain,
    ( spl16_140
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1470,f990,f962,f166,f159,f152,f1509])).

fof(f1509,plain,
    ( spl16_140
  <=> r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK10(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_140])])).

fof(f1470,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f683,f684,f963,f991,f104])).

fof(f1504,plain,
    ( spl16_138
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_80
    | ~ spl16_88
    | ~ spl16_110 ),
    inference(avatar_split_clause,[],[f1471,f1353,f990,f962,f166,f152,f1502])).

fof(f1502,plain,
    ( spl16_138
  <=> r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_138])])).

fof(f1471,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_80
    | ~ spl16_88
    | ~ spl16_110 ),
    inference(unit_resulting_resolution,[],[f167,f153,f1354,f963,f991,f279])).

fof(f1497,plain,
    ( ~ spl16_137
    | spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1472,f990,f983,f166,f152,f145,f1495])).

fof(f1472,plain,
    ( ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f153,f167,f146,f984,f991,f612])).

fof(f1490,plain,
    ( spl16_134
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1473,f990,f983,f264,f173,f166,f159,f152,f1488])).

fof(f1473,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,sK1)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_86
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f984,f991,f639])).

fof(f1483,plain,
    ( spl16_132
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(avatar_split_clause,[],[f1474,f990,f962,f264,f173,f166,f159,f152,f1481])).

fof(f1474,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_80
    | ~ spl16_88 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f963,f991,f639])).

fof(f1456,plain,
    ( ~ spl16_131
    | spl16_29
    | spl16_77 ),
    inference(avatar_split_clause,[],[f1449,f948,f264,f1454])).

fof(f1454,plain,
    ( spl16_131
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_131])])).

fof(f948,plain,
    ( spl16_77
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_77])])).

fof(f1449,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_29
    | ~ spl16_77 ),
    inference(unit_resulting_resolution,[],[f297,f949,f123])).

fof(f949,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_77 ),
    inference(avatar_component_clause,[],[f948])).

fof(f1448,plain,
    ( spl16_128
    | ~ spl16_86 ),
    inference(avatar_split_clause,[],[f1440,f983,f1446])).

fof(f1446,plain,
    ( spl16_128
  <=> m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_128])])).

fof(f1440,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_86 ),
    inference(unit_resulting_resolution,[],[f984,f122])).

fof(f1437,plain,
    ( ~ spl16_127
    | spl16_29
    | spl16_83 ),
    inference(avatar_split_clause,[],[f1430,f969,f264,f1435])).

fof(f1435,plain,
    ( spl16_127
  <=> ~ m1_subset_1(sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_127])])).

fof(f969,plain,
    ( spl16_83
  <=> ~ r2_hidden(sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_83])])).

fof(f1430,plain,
    ( ~ m1_subset_1(sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_29
    | ~ spl16_83 ),
    inference(unit_resulting_resolution,[],[f297,f970,f123])).

fof(f970,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_83 ),
    inference(avatar_component_clause,[],[f969])).

fof(f1429,plain,
    ( spl16_124
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_110 ),
    inference(avatar_split_clause,[],[f1379,f1353,f166,f152,f1427])).

fof(f1379,plain,
    ( m1_subset_1(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_110 ),
    inference(unit_resulting_resolution,[],[f167,f153,f1354,f108])).

fof(f1422,plain,
    ( spl16_122
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_110 ),
    inference(avatar_split_clause,[],[f1380,f1353,f166,f152,f1420])).

fof(f1420,plain,
    ( spl16_122
  <=> r1_lattice3(sK0,u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_122])])).

fof(f1380,plain,
    ( r1_lattice3(sK0,u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_110 ),
    inference(unit_resulting_resolution,[],[f167,f153,f1354,f109])).

fof(f1415,plain,
    ( spl16_120
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29
    | ~ spl16_110 ),
    inference(avatar_split_clause,[],[f1381,f1353,f264,f173,f166,f159,f152,f1413])).

fof(f1413,plain,
    ( spl16_120
  <=> r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK8(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_120])])).

fof(f1381,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_110 ),
    inference(unit_resulting_resolution,[],[f167,f153,f430,f431,f1354,f110])).

fof(f1408,plain,
    ( spl16_118
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110 ),
    inference(avatar_split_clause,[],[f1382,f1353,f264,f166,f152,f1406])).

fof(f1382,plain,
    ( r2_hidden(sK8(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110 ),
    inference(unit_resulting_resolution,[],[f153,f167,f297,f1354,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(resolution,[],[f108,f123])).

fof(f1401,plain,
    ( spl16_116
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110 ),
    inference(avatar_split_clause,[],[f1384,f1353,f264,f166,f152,f1399])).

fof(f1399,plain,
    ( spl16_116
  <=> r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK11(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_116])])).

fof(f1384,plain,
    ( r1_orders_2(sK0,sK8(sK0,u1_struct_0(sK0)),sK11(u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110 ),
    inference(unit_resulting_resolution,[],[f167,f153,f120,f370,f1354,f279])).

fof(f1394,plain,
    ( ~ spl16_115
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | ~ spl16_110 ),
    inference(avatar_split_clause,[],[f1387,f1353,f264,f166,f152,f1392])).

fof(f1387,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK8(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_110 ),
    inference(unit_resulting_resolution,[],[f153,f167,f297,f1354,f394])).

fof(f394,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(u1_struct_0(X0),sK8(X0,X1))
      | ~ v5_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f223,f121])).

fof(f1378,plain,
    ( ~ spl16_113
    | spl16_29
    | spl16_79 ),
    inference(avatar_split_clause,[],[f1370,f955,f264,f1376])).

fof(f1376,plain,
    ( spl16_113
  <=> ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_113])])).

fof(f955,plain,
    ( spl16_79
  <=> ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_79])])).

fof(f1370,plain,
    ( ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_29
    | ~ spl16_79 ),
    inference(unit_resulting_resolution,[],[f297,f956,f123])).

fof(f956,plain,
    ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_79 ),
    inference(avatar_component_clause,[],[f955])).

fof(f1355,plain,
    ( spl16_110
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1346,f264,f173,f166,f159,f152,f1353])).

fof(f1346,plain,
    ( r2_yellow_0(sK0,u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f430,f431,f444,f612])).

fof(f1242,plain,
    ( ~ spl16_109
    | spl16_29
    | spl16_91 ),
    inference(avatar_split_clause,[],[f1235,f1150,f264,f1240])).

fof(f1240,plain,
    ( spl16_109
  <=> ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_109])])).

fof(f1150,plain,
    ( spl16_91
  <=> ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_91])])).

fof(f1235,plain,
    ( ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,sK1)),sK1)
    | ~ spl16_29
    | ~ spl16_91 ),
    inference(unit_resulting_resolution,[],[f297,f1151,f123])).

fof(f1151,plain,
    ( ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,sK1)),sK1)
    | ~ spl16_91 ),
    inference(avatar_component_clause,[],[f1150])).

fof(f1202,plain,
    ( ~ spl16_5
    | spl16_106
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1145,f264,f173,f166,f159,f152,f1200,f149])).

fof(f1145,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,X3)),X2)
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X3)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(resolution,[],[f431,f100])).

fof(f1198,plain,
    ( spl16_104
    | ~ spl16_9
    | ~ spl16_5
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1144,f264,f173,f166,f159,f152,f149,f163,f1196])).

fof(f1196,plain,
    ( spl16_104
  <=> ! [X1] :
        ( ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,X1)),X1)
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X1)),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_104])])).

fof(f1144,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,X1)),X1)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(sK11(a_2_0_yellow_0(sK0,X1)),u1_struct_0(sK0)) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(resolution,[],[f431,f612])).

fof(f1194,plain,
    ( spl16_102
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1133,f264,f173,f166,f159,f152,f145,f1192])).

fof(f1133,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f430,f431,f111])).

fof(f1187,plain,
    ( spl16_100
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1134,f264,f173,f166,f159,f152,f145,f1185])).

fof(f1134,plain,
    ( r1_lattice3(sK0,sK1,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f430,f431,f112])).

fof(f1180,plain,
    ( ~ spl16_99
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1135,f264,f173,f166,f159,f152,f145,f1178])).

fof(f1135,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),sK11(a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f430,f431,f113])).

fof(f1173,plain,
    ( spl16_96
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1138,f264,f173,f166,f159,f152,f145,f1171])).

fof(f1138,plain,
    ( r2_hidden(sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f146,f153,f167,f297,f430,f431,f305])).

fof(f1166,plain,
    ( ~ spl16_95
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1139,f264,f173,f166,f159,f152,f145,f1164])).

fof(f1139,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(sK0,sK1,sK11(a_2_0_yellow_0(sK0,sK1))))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f146,f167,f297,f430,f431,f445])).

fof(f1159,plain,
    ( ~ spl16_93
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1140,f264,f173,f166,f159,f152,f145,f1157])).

fof(f1140,plain,
    ( ~ r2_lattice3(sK0,u1_struct_0(sK0),sK11(a_2_0_yellow_0(sK0,sK1)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f167,f146,f297,f430,f431,f605])).

fof(f1152,plain,
    ( ~ spl16_91
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f1141,f264,f173,f166,f159,f152,f145,f1150])).

fof(f1141,plain,
    ( ~ r2_hidden(sK11(a_2_0_yellow_0(sK0,sK1)),sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f146,f167,f430,f431,f612])).

fof(f1007,plain,
    ( spl16_22
    | ~ spl16_63
    | spl16_64
    | ~ spl16_9
    | ~ spl16_5
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29 ),
    inference(avatar_split_clause,[],[f935,f264,f159,f152,f149,f163,f766,f763,f220])).

fof(f935,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_lattice3(sK0,X1,sK4(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29 ),
    inference(resolution,[],[f699,f605])).

fof(f1006,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | spl16_23
    | spl16_63 ),
    inference(avatar_contradiction_clause,[],[f999])).

fof(f999,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_23
    | ~ spl16_63 ),
    inference(unit_resulting_resolution,[],[f253,f764,f122])).

fof(f764,plain,
    ( ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl16_63 ),
    inference(avatar_component_clause,[],[f763])).

fof(f1005,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | spl16_63 ),
    inference(avatar_contradiction_clause,[],[f996])).

fof(f996,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_63 ),
    inference(unit_resulting_resolution,[],[f153,f160,f764,f94])).

fof(f1004,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | spl16_63 ),
    inference(avatar_contradiction_clause,[],[f993])).

fof(f993,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_63 ),
    inference(unit_resulting_resolution,[],[f209,f764])).

fof(f1003,plain,
    ( ~ spl16_4
    | ~ spl16_6
    | spl16_63 ),
    inference(avatar_contradiction_clause,[],[f1000])).

fof(f1000,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_63 ),
    inference(resolution,[],[f764,f209])).

fof(f992,plain,
    ( spl16_88
    | ~ spl16_4
    | ~ spl16_6
    | spl16_61 ),
    inference(avatar_split_clause,[],[f937,f756,f159,f152,f990])).

fof(f937,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_61 ),
    inference(unit_resulting_resolution,[],[f153,f209,f757,f101])).

fof(f985,plain,
    ( spl16_86
    | ~ spl16_4
    | ~ spl16_6
    | spl16_61 ),
    inference(avatar_split_clause,[],[f938,f756,f159,f152,f983])).

fof(f938,plain,
    ( r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),sK1)
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_61 ),
    inference(unit_resulting_resolution,[],[f153,f209,f757,f102])).

fof(f978,plain,
    ( ~ spl16_85
    | ~ spl16_4
    | ~ spl16_6
    | spl16_61 ),
    inference(avatar_split_clause,[],[f939,f756,f159,f152,f976])).

fof(f939,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,u1_struct_0(sK0)),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_61 ),
    inference(unit_resulting_resolution,[],[f153,f209,f757,f103])).

fof(f971,plain,
    ( ~ spl16_83
    | ~ spl16_4
    | ~ spl16_6
    | spl16_61 ),
    inference(avatar_split_clause,[],[f940,f756,f159,f152,f969])).

fof(f940,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_61 ),
    inference(unit_resulting_resolution,[],[f153,f209,f757,f230])).

fof(f964,plain,
    ( spl16_80
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | spl16_61 ),
    inference(avatar_split_clause,[],[f941,f756,f264,f159,f152,f962])).

fof(f941,plain,
    ( r2_hidden(sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_61 ),
    inference(unit_resulting_resolution,[],[f153,f297,f209,f757,f245])).

fof(f957,plain,
    ( ~ spl16_79
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_61 ),
    inference(avatar_split_clause,[],[f942,f756,f173,f166,f159,f152,f955])).

fof(f942,plain,
    ( ~ r2_hidden(sK4(sK0,u1_struct_0(sK0)),a_2_0_yellow_0(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_61 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f757,f274])).

fof(f950,plain,
    ( ~ spl16_77
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29
    | spl16_61 ),
    inference(avatar_split_clause,[],[f943,f756,f264,f159,f152,f948])).

fof(f943,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,sK1,sK4(sK0,u1_struct_0(sK0))))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29
    | ~ spl16_61 ),
    inference(unit_resulting_resolution,[],[f153,f297,f209,f757,f409])).

fof(f849,plain,
    ( spl16_22
    | ~ spl16_73
    | spl16_74
    | ~ spl16_9
    | ~ spl16_5
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f824,f166,f159,f152,f149,f163,f847,f844,f220])).

fof(f824,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_lattice3(sK0,X1,sK10(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(sK10(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(resolution,[],[f684,f605])).

fof(f839,plain,
    ( spl16_70
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29 ),
    inference(avatar_split_clause,[],[f815,f264,f166,f159,f152,f837])).

fof(f837,plain,
    ( spl16_70
  <=> r1_orders_2(sK0,sK11(u1_struct_0(sK0)),sK10(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_70])])).

fof(f815,plain,
    ( r1_orders_2(sK0,sK11(u1_struct_0(sK0)),sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f370,f120,f683,f684,f104])).

fof(f832,plain,
    ( ~ spl16_69
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29 ),
    inference(avatar_split_clause,[],[f819,f264,f166,f159,f152,f145,f830])).

fof(f819,plain,
    ( ~ r1_lattice3(sK0,sK1,sK10(sK0,u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f297,f683,f684,f605])).

fof(f784,plain,
    ( spl16_66
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_11
    | spl16_29 ),
    inference(avatar_split_clause,[],[f769,f264,f173,f166,f159,f152,f782])).

fof(f782,plain,
    ( spl16_66
  <=> r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK11(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_66])])).

fof(f769,plain,
    ( r1_orders_2(sK0,sK11(a_2_0_yellow_0(sK0,u1_struct_0(sK0))),sK11(u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f174,f167,f160,f153,f370,f120,f370,f639])).

fof(f768,plain,
    ( spl16_22
    | ~ spl16_63
    | spl16_64
    | ~ spl16_9
    | ~ spl16_5
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(avatar_split_clause,[],[f748,f159,f152,f149,f163,f766,f763,f220])).

fof(f748,plain,
    ( ! [X7] :
        ( ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_lattice3(sK0,X7,sK4(sK0,u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X7)
        | ~ m1_subset_1(sK4(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(resolution,[],[f605,f211])).

fof(f758,plain,
    ( ~ spl16_61
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29 ),
    inference(avatar_split_clause,[],[f744,f264,f166,f159,f152,f145,f756])).

fof(f744,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f167,f153,f146,f297,f209,f211,f605])).

fof(f582,plain,
    ( ~ spl16_59
    | spl16_29
    | spl16_55 ),
    inference(avatar_split_clause,[],[f575,f540,f264,f580])).

fof(f580,plain,
    ( spl16_59
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_59])])).

fof(f540,plain,
    ( spl16_55
  <=> ~ r2_hidden(u1_struct_0(sK0),sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_55])])).

fof(f575,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK10(sK0,sK1))
    | ~ spl16_29
    | ~ spl16_55 ),
    inference(unit_resulting_resolution,[],[f297,f541,f123])).

fof(f541,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK10(sK0,sK1))
    | ~ spl16_55 ),
    inference(avatar_component_clause,[],[f540])).

fof(f558,plain,
    ( ~ spl16_49
    | spl16_33 ),
    inference(avatar_split_clause,[],[f556,f326,f449])).

fof(f449,plain,
    ( spl16_49
  <=> ~ r2_hidden(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_49])])).

fof(f326,plain,
    ( spl16_33
  <=> ~ m1_subset_1(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_33])])).

fof(f556,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl16_33 ),
    inference(resolution,[],[f327,f122])).

fof(f327,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl16_33 ),
    inference(avatar_component_clause,[],[f326])).

fof(f557,plain,
    ( ~ spl16_49
    | spl16_33 ),
    inference(avatar_split_clause,[],[f554,f326,f449])).

fof(f554,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl16_33 ),
    inference(unit_resulting_resolution,[],[f327,f122])).

fof(f551,plain,
    ( ~ spl16_55
    | ~ spl16_44 ),
    inference(avatar_split_clause,[],[f535,f380,f540])).

fof(f380,plain,
    ( spl16_44
  <=> r2_hidden(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).

fof(f535,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK10(sK0,sK1))
    | ~ spl16_44 ),
    inference(resolution,[],[f381,f121])).

fof(f381,plain,
    ( r2_hidden(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl16_44 ),
    inference(avatar_component_clause,[],[f380])).

fof(f550,plain,
    ( spl16_56
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_38
    | ~ spl16_44 ),
    inference(avatar_split_clause,[],[f531,f380,f353,f159,f152,f548])).

fof(f548,plain,
    ( spl16_56
  <=> r1_orders_2(sK0,sK10(sK0,sK1),sK4(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_56])])).

fof(f353,plain,
    ( spl16_38
  <=> m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).

fof(f531,plain,
    ( r1_orders_2(sK0,sK10(sK0,sK1),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_38
    | ~ spl16_44 ),
    inference(unit_resulting_resolution,[],[f153,f209,f211,f354,f381,f104])).

fof(f354,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl16_38 ),
    inference(avatar_component_clause,[],[f353])).

fof(f543,plain,
    ( ~ spl16_55
    | ~ spl16_44 ),
    inference(avatar_split_clause,[],[f532,f380,f540])).

fof(f532,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK10(sK0,sK1))
    | ~ spl16_44 ),
    inference(unit_resulting_resolution,[],[f381,f121])).

fof(f542,plain,
    ( ~ spl16_55
    | ~ spl16_44 ),
    inference(avatar_split_clause,[],[f533,f380,f540])).

fof(f533,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK10(sK0,sK1))
    | ~ spl16_44 ),
    inference(unit_resulting_resolution,[],[f381,f121])).

fof(f530,plain,
    ( spl16_52
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_38
    | ~ spl16_40 ),
    inference(avatar_split_clause,[],[f515,f360,f353,f159,f152,f528])).

fof(f528,plain,
    ( spl16_52
  <=> r1_orders_2(sK0,sK4(sK0,sK1),sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_52])])).

fof(f360,plain,
    ( spl16_40
  <=> r2_lattice3(sK0,sK1,sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_40])])).

fof(f515,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1),sK10(sK0,sK1))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_38
    | ~ spl16_40 ),
    inference(unit_resulting_resolution,[],[f153,f160,f354,f361,f96])).

fof(f361,plain,
    ( r2_lattice3(sK0,sK1,sK10(sK0,sK1))
    | ~ spl16_40 ),
    inference(avatar_component_clause,[],[f360])).

fof(f523,plain,
    ( spl16_50
    | ~ spl16_0
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_40 ),
    inference(avatar_split_clause,[],[f516,f360,f353,f166,f152,f136,f521])).

fof(f521,plain,
    ( spl16_50
  <=> r1_orders_2(sK0,sK10(sK0,sK1),sK10(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_50])])).

fof(f136,plain,
    ( spl16_0
  <=> r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_0])])).

fof(f516,plain,
    ( r1_orders_2(sK0,sK10(sK0,sK1),sK10(sK0,sK1))
    | ~ spl16_0
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_40 ),
    inference(unit_resulting_resolution,[],[f167,f153,f137,f354,f361,f116])).

fof(f137,plain,
    ( r1_yellow_0(sK0,sK1)
    | ~ spl16_0 ),
    inference(avatar_component_clause,[],[f136])).

fof(f508,plain,
    ( ~ spl16_39
    | spl16_29
    | spl16_45 ),
    inference(avatar_split_clause,[],[f495,f383,f264,f350])).

fof(f350,plain,
    ( spl16_39
  <=> ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).

fof(f383,plain,
    ( spl16_45
  <=> ~ r2_hidden(sK10(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).

fof(f495,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl16_29
    | ~ spl16_45 ),
    inference(unit_resulting_resolution,[],[f297,f384,f123])).

fof(f384,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl16_45 ),
    inference(avatar_component_clause,[],[f383])).

fof(f507,plain,
    ( ~ spl16_1
    | ~ spl16_4
    | ~ spl16_8
    | spl16_29
    | spl16_45 ),
    inference(avatar_split_clause,[],[f494,f383,f264,f166,f152,f139])).

fof(f139,plain,
    ( spl16_1
  <=> ~ r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f494,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_29
    | ~ spl16_45 ),
    inference(unit_resulting_resolution,[],[f167,f153,f297,f384,f224])).

fof(f506,plain,
    ( ~ spl16_1
    | spl16_22
    | ~ spl16_9
    | ~ spl16_5
    | spl16_45 ),
    inference(avatar_split_clause,[],[f496,f383,f149,f163,f220,f139])).

fof(f496,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1)
    | ~ spl16_45 ),
    inference(resolution,[],[f384,f224])).

fof(f505,plain,
    ( ~ spl16_35
    | spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_32 ),
    inference(avatar_split_clause,[],[f502,f329,f166,f159,f152,f139,f333])).

fof(f333,plain,
    ( spl16_35
  <=> ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1,sK4(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_35])])).

fof(f329,plain,
    ( spl16_32
  <=> m1_subset_1(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_32])])).

fof(f502,plain,
    ( ~ r2_lattice3(sK0,sK1,sK9(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_32 ),
    inference(unit_resulting_resolution,[],[f160,f153,f167,f140,f211,f209,f330,f319])).

fof(f330,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl16_32 ),
    inference(avatar_component_clause,[],[f329])).

fof(f140,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | ~ spl16_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f454,plain,
    ( spl16_48
    | spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | spl16_29 ),
    inference(avatar_split_clause,[],[f446,f264,f166,f159,f152,f139,f452])).

fof(f452,plain,
    ( spl16_48
  <=> r2_hidden(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_48])])).

fof(f446,plain,
    ( r2_hidden(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f140,f153,f167,f297,f211,f209,f313])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(resolution,[],[f117,f123])).

fof(f438,plain,
    ( spl16_46
    | ~ spl16_4
    | ~ spl16_6
    | spl16_29 ),
    inference(avatar_split_clause,[],[f418,f264,f159,f152,f436])).

fof(f436,plain,
    ( spl16_46
  <=> r1_orders_2(sK0,sK11(u1_struct_0(sK0)),sK4(sK0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_46])])).

fof(f418,plain,
    ( r1_orders_2(sK0,sK11(u1_struct_0(sK0)),sK4(sK0,u1_struct_0(sK0)))
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f153,f209,f211,f120,f370,f104])).

fof(f386,plain,
    ( ~ spl16_45
    | spl16_39 ),
    inference(avatar_split_clause,[],[f378,f350,f383])).

fof(f378,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl16_39 ),
    inference(resolution,[],[f351,f122])).

fof(f351,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl16_39 ),
    inference(avatar_component_clause,[],[f350])).

fof(f385,plain,
    ( ~ spl16_45
    | spl16_39 ),
    inference(avatar_split_clause,[],[f376,f350,f383])).

fof(f376,plain,
    ( ~ r2_hidden(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl16_39 ),
    inference(unit_resulting_resolution,[],[f351,f122])).

fof(f369,plain,
    ( spl16_42
    | ~ spl16_0
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f346,f166,f159,f152,f136,f367])).

fof(f367,plain,
    ( spl16_42
  <=> r1_orders_2(sK0,sK10(sK0,sK1),sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_42])])).

fof(f346,plain,
    ( r1_orders_2(sK0,sK10(sK0,sK1),sK4(sK0,sK1))
    | ~ spl16_0
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f167,f153,f211,f209,f137,f116])).

fof(f362,plain,
    ( spl16_40
    | ~ spl16_0
    | ~ spl16_4
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f347,f166,f152,f136,f360])).

fof(f347,plain,
    ( r2_lattice3(sK0,sK1,sK10(sK0,sK1))
    | ~ spl16_0
    | ~ spl16_4
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f167,f153,f137,f115])).

fof(f355,plain,
    ( spl16_38
    | ~ spl16_0
    | ~ spl16_4
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f348,f166,f152,f136,f353])).

fof(f348,plain,
    ( m1_subset_1(sK10(sK0,sK1),u1_struct_0(sK0))
    | ~ spl16_0
    | ~ spl16_4
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f167,f153,f137,f114])).

fof(f345,plain,
    ( ~ spl16_37
    | spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f321,f166,f159,f152,f139,f343])).

fof(f343,plain,
    ( spl16_37
  <=> ~ r1_orders_2(sK0,sK4(sK0,sK1),sK9(sK0,sK1,sK4(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_37])])).

fof(f321,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1),sK9(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f167,f153,f140,f209,f211,f119])).

fof(f338,plain,
    ( spl16_34
    | spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f322,f166,f159,f152,f139,f336])).

fof(f336,plain,
    ( spl16_34
  <=> r2_lattice3(sK0,sK1,sK9(sK0,sK1,sK4(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).

fof(f322,plain,
    ( r2_lattice3(sK0,sK1,sK9(sK0,sK1,sK4(sK0,sK1)))
    | ~ spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f167,f153,f140,f209,f211,f118])).

fof(f331,plain,
    ( spl16_32
    | spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(avatar_split_clause,[],[f323,f166,f159,f152,f139,f329])).

fof(f323,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK4(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl16_1
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f167,f153,f140,f209,f211,f117])).

fof(f304,plain,
    ( spl16_30
    | spl16_29 ),
    inference(avatar_split_clause,[],[f295,f264,f302])).

fof(f302,plain,
    ( spl16_30
  <=> r2_hidden(sK11(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_30])])).

fof(f295,plain,
    ( r2_hidden(sK11(k1_xboole_0),k1_xboole_0)
    | ~ spl16_29 ),
    inference(unit_resulting_resolution,[],[f120,f265,f123])).

fof(f269,plain,
    ( spl16_28
    | ~ spl16_22
    | ~ spl16_24 ),
    inference(avatar_split_clause,[],[f262,f242,f220,f267])).

fof(f267,plain,
    ( spl16_28
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_28])])).

fof(f242,plain,
    ( spl16_24
  <=> u1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_24])])).

fof(f262,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl16_22
    | ~ spl16_24 ),
    inference(forward_demodulation,[],[f221,f243])).

fof(f243,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl16_24 ),
    inference(avatar_component_clause,[],[f242])).

fof(f221,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f260,plain,
    ( spl16_26
    | spl16_23 ),
    inference(avatar_split_clause,[],[f252,f217,f258])).

fof(f258,plain,
    ( spl16_26
  <=> r2_hidden(sK11(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_26])])).

fof(f252,plain,
    ( r2_hidden(sK11(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl16_23 ),
    inference(unit_resulting_resolution,[],[f120,f218,f123])).

fof(f244,plain,
    ( spl16_24
    | ~ spl16_22 ),
    inference(avatar_split_clause,[],[f237,f220,f242])).

fof(f237,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl16_22 ),
    inference(unit_resulting_resolution,[],[f221,f92])).

fof(f222,plain,
    ( spl16_20
    | spl16_22
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(avatar_split_clause,[],[f212,f159,f152,f220,f214])).

fof(f214,plain,
    ( spl16_20
  <=> ! [X0] : r2_hidden(sK4(sK0,X0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_20])])).

fof(f212,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK4(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(resolution,[],[f209,f123])).

fof(f205,plain,
    ( spl16_18
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f190,f152,f203])).

fof(f203,plain,
    ( spl16_18
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_18])])).

fof(f190,plain,
    ( l1_struct_0(sK0)
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f153,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',dt_l1_orders_2)).

fof(f198,plain,
    ( spl16_16
    | ~ spl16_14 ),
    inference(avatar_split_clause,[],[f191,f187,f196])).

fof(f196,plain,
    ( spl16_16
  <=> l1_struct_0(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).

fof(f187,plain,
    ( spl16_14
  <=> l1_orders_2(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).

fof(f191,plain,
    ( l1_struct_0(sK15)
    | ~ spl16_14 ),
    inference(unit_resulting_resolution,[],[f188,f93])).

fof(f188,plain,
    ( l1_orders_2(sK15)
    | ~ spl16_14 ),
    inference(avatar_component_clause,[],[f187])).

fof(f189,plain,(
    spl16_14 ),
    inference(avatar_split_clause,[],[f133,f187])).

fof(f133,plain,(
    l1_orders_2(sK15) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    l1_orders_2(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f12,f85])).

fof(f85,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK15) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',existence_l1_orders_2)).

fof(f182,plain,(
    spl16_12 ),
    inference(avatar_split_clause,[],[f132,f180])).

fof(f180,plain,
    ( spl16_12
  <=> l1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).

fof(f132,plain,(
    l1_struct_0(sK14) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    l1_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f13,f83])).

fof(f83,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK14) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',existence_l1_struct_0)).

fof(f175,plain,(
    ~ spl16_11 ),
    inference(avatar_split_clause,[],[f87,f173])).

fof(f87,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ r2_yellow_0(sK0,sK1)
      | ~ r1_yellow_0(sK0,sK1) )
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_yellow_0(sK0,X1)
          | ~ r1_yellow_0(sK0,X1) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          | ~ r1_yellow_0(X0,X1) )
     => ( ~ r2_yellow_0(X0,sK1)
        | ~ r1_yellow_0(X0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          | ~ r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          | ~ r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( r2_yellow_0(X0,X1)
            & r1_yellow_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t17_yellow_0.p',t17_yellow_0)).

fof(f168,plain,(
    spl16_8 ),
    inference(avatar_split_clause,[],[f88,f166])).

fof(f88,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f161,plain,(
    spl16_6 ),
    inference(avatar_split_clause,[],[f89,f159])).

fof(f89,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f154,plain,(
    spl16_4 ),
    inference(avatar_split_clause,[],[f90,f152])).

fof(f90,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f147,plain,
    ( ~ spl16_1
    | ~ spl16_3 ),
    inference(avatar_split_clause,[],[f91,f145,f139])).

fof(f91,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
