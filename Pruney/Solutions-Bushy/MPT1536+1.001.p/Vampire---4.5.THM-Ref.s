%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1536+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:02 EST 2020

% Result     : Theorem 11.42s
% Output     : Refutation 11.42s
% Verified   : 
% Statistics : Number of formulae       :  486 (1278 expanded)
%              Number of leaves         :   87 ( 644 expanded)
%              Depth                    :   11
%              Number of atoms          : 2473 (6134 expanded)
%              Number of equality atoms :  178 ( 652 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f110,f115,f120,f121,f131,f136,f141,f148,f159,f176,f181,f189,f194,f200,f213,f250,f257,f285,f486,f646,f705,f1011,f1128,f1642,f1897,f1913,f1939,f1972,f1996,f2012,f2045,f2068,f2089,f2262,f2280,f2284,f2309,f2330,f2334,f2454,f2710,f2715,f2728,f2740,f2749,f2844,f2856,f2867,f2869,f3022,f3026,f3046,f3093,f3103,f3152,f3160,f3171,f3178,f3180,f3219,f3458,f3474,f3482,f3630,f3636,f3644,f3646,f3658,f3752,f3753,f4206,f4227,f4251,f4258,f4327,f4389,f4395,f4398,f4400,f4413,f4443,f4636,f4685,f4686,f4689,f4690,f4708,f4850,f4852,f5159])).

fof(f5159,plain,
    ( spl11_4
    | ~ spl11_3
    | ~ spl11_274
    | ~ spl11_276
    | ~ spl11_294
    | ~ spl11_16
    | ~ spl11_302 ),
    inference(avatar_split_clause,[],[f5158,f3100,f178,f3014,f2896,f2889,f98,f103])).

fof(f103,plain,
    ( spl11_4
  <=> r2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f98,plain,
    ( spl11_3
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f2889,plain,
    ( spl11_274
  <=> r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_274])])).

fof(f2896,plain,
    ( spl11_276
  <=> r1_lattice3(sK1,sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_276])])).

fof(f3014,plain,
    ( spl11_294
  <=> m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_294])])).

fof(f178,plain,
    ( spl11_16
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f3100,plain,
    ( spl11_302
  <=> sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_302])])).

fof(f5158,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | ~ spl11_302 ),
    inference(forward_demodulation,[],[f5151,f180])).

fof(f180,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f5151,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_302 ),
    inference(trivial_inequality_removal,[],[f5147])).

fof(f5147,plain,
    ( sK3(sK0,sK2) != sK3(sK0,sK2)
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_302 ),
    inference(superposition,[],[f49,f3101])).

fof(f3101,plain,
    ( sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ spl11_302 ),
    inference(avatar_component_clause,[],[f3100])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_0)).

fof(f4852,plain,
    ( spl11_4
    | ~ spl11_3
    | ~ spl11_274
    | ~ spl11_276
    | ~ spl11_294
    | ~ spl11_16
    | spl11_315 ),
    inference(avatar_split_clause,[],[f4851,f3203,f178,f3014,f2896,f2889,f98,f103])).

fof(f3203,plain,
    ( spl11_315
  <=> r1_lattice3(sK1,sK2,sK5(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_315])])).

fof(f4851,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_315 ),
    inference(forward_demodulation,[],[f4847,f180])).

fof(f4847,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | spl11_315 ),
    inference(resolution,[],[f3205,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3205,plain,
    ( ~ r1_lattice3(sK1,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | spl11_315 ),
    inference(avatar_component_clause,[],[f3203])).

fof(f4850,plain,
    ( spl11_4
    | ~ spl11_3
    | ~ spl11_276
    | ~ spl11_294
    | spl11_300
    | ~ spl11_16
    | spl11_315 ),
    inference(avatar_split_clause,[],[f4849,f3203,f178,f3085,f3014,f2896,f98,f103])).

fof(f3085,plain,
    ( spl11_300
  <=> m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_300])])).

fof(f4849,plain,
    ( m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_315 ),
    inference(forward_demodulation,[],[f4848,f180])).

fof(f4848,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_315 ),
    inference(forward_demodulation,[],[f4845,f180])).

fof(f4845,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | spl11_315 ),
    inference(resolution,[],[f3205,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4708,plain,
    ( ~ spl11_6
    | spl11_302
    | ~ spl11_1
    | ~ spl11_317
    | ~ spl11_312
    | spl11_350 ),
    inference(avatar_split_clause,[],[f4151,f3466,f3175,f3212,f88,f3100,f112])).

fof(f112,plain,
    ( spl11_6
  <=> r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f88,plain,
    ( spl11_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f3212,plain,
    ( spl11_317
  <=> r1_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_317])])).

fof(f3175,plain,
    ( spl11_312
  <=> m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_312])])).

fof(f3466,plain,
    ( spl11_350
  <=> m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_350])])).

fof(f4151,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK2)
    | spl11_350 ),
    inference(resolution,[],[f3468,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | sK3(X0,X1) = X3
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3468,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | spl11_350 ),
    inference(avatar_component_clause,[],[f3466])).

fof(f4690,plain,
    ( ~ spl11_230
    | ~ spl11_258
    | spl11_260
    | spl11_7
    | ~ spl11_188
    | spl11_273 ),
    inference(avatar_split_clause,[],[f4687,f2864,f1640,f117,f2707,f2696,f2075])).

fof(f2075,plain,
    ( spl11_230
  <=> m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_230])])).

fof(f2696,plain,
    ( spl11_258
  <=> r2_lattice3(sK1,sK2,sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_258])])).

fof(f2707,plain,
    ( spl11_260
  <=> m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_260])])).

fof(f117,plain,
    ( spl11_7
  <=> r1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1640,plain,
    ( spl11_188
  <=> ! [X1,X0] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_188])])).

fof(f2864,plain,
    ( spl11_273
  <=> m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_273])])).

fof(f4687,plain,
    ( r1_yellow_0(sK1,sK2)
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ spl11_188
    | spl11_273 ),
    inference(resolution,[],[f2865,f1641])).

fof(f1641,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_188 ),
    inference(avatar_component_clause,[],[f1640])).

fof(f2865,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | spl11_273 ),
    inference(avatar_component_clause,[],[f2864])).

fof(f4689,plain,
    ( ~ spl11_230
    | ~ spl11_258
    | ~ spl11_257
    | spl11_7
    | ~ spl11_131
    | spl11_273 ),
    inference(avatar_split_clause,[],[f4688,f2864,f1126,f117,f2692,f2696,f2075])).

fof(f2692,plain,
    ( spl11_257
  <=> r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_257])])).

fof(f1126,plain,
    ( spl11_131
  <=> ! [X1,X0] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | ~ r1_orders_2(sK1,X1,sK8(sK1,X0,X1))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_131])])).

fof(f4688,plain,
    ( r1_yellow_0(sK1,sK2)
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ spl11_131
    | spl11_273 ),
    inference(resolution,[],[f2865,f1127])).

fof(f1127,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | ~ r1_orders_2(sK1,X1,sK8(sK1,X0,X1))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_131 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f4686,plain,
    ( ~ spl11_410
    | ~ spl11_273
    | ~ spl11_215
    | spl11_407 ),
    inference(avatar_split_clause,[],[f4659,f4199,f1937,f2864,f4215])).

fof(f4215,plain,
    ( spl11_410
  <=> r2_lattice3(sK1,sK2,sK9(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_410])])).

fof(f1937,plain,
    ( spl11_215
  <=> ! [X1,X0] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_215])])).

fof(f4199,plain,
    ( spl11_407
  <=> r2_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_407])])).

fof(f4659,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl11_215
    | spl11_407 ),
    inference(resolution,[],[f4201,f1938])).

fof(f1938,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1) )
    | ~ spl11_215 ),
    inference(avatar_component_clause,[],[f1937])).

fof(f4201,plain,
    ( ~ r2_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | spl11_407 ),
    inference(avatar_component_clause,[],[f4199])).

fof(f4685,plain,
    ( spl11_7
    | ~ spl11_3
    | ~ spl11_257
    | ~ spl11_258
    | ~ spl11_230
    | ~ spl11_16
    | spl11_410 ),
    inference(avatar_split_clause,[],[f4684,f4215,f178,f2075,f2696,f2692,f98,f117])).

fof(f4684,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_410 ),
    inference(forward_demodulation,[],[f4681,f180])).

fof(f4681,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | spl11_410 ),
    inference(resolution,[],[f4217,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_yellow_0)).

fof(f4217,plain,
    ( ~ r2_lattice3(sK1,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | spl11_410 ),
    inference(avatar_component_clause,[],[f4215])).

fof(f4636,plain,
    ( spl11_7
    | ~ spl11_3
    | ~ spl11_257
    | ~ spl11_258
    | ~ spl11_230
    | ~ spl11_16
    | ~ spl11_263 ),
    inference(avatar_split_clause,[],[f4635,f2725,f178,f2075,f2696,f2692,f98,f117])).

fof(f2725,plain,
    ( spl11_263
  <=> sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_263])])).

fof(f4635,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | ~ spl11_263 ),
    inference(forward_demodulation,[],[f4624,f180])).

fof(f4624,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_263 ),
    inference(trivial_inequality_removal,[],[f4620])).

fof(f4620,plain,
    ( sK7(sK0,sK2) != sK7(sK0,sK2)
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_263 ),
    inference(superposition,[],[f67,f2726])).

fof(f2726,plain,
    ( sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ spl11_263 ),
    inference(avatar_component_clause,[],[f2725])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4443,plain,
    ( spl11_7
    | ~ spl11_3
    | ~ spl11_258
    | ~ spl11_230
    | spl11_260
    | ~ spl11_16
    | spl11_410 ),
    inference(avatar_split_clause,[],[f4442,f4215,f178,f2707,f2075,f2696,f98,f117])).

fof(f4442,plain,
    ( m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_410 ),
    inference(forward_demodulation,[],[f4441,f180])).

fof(f4441,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_410 ),
    inference(forward_demodulation,[],[f4438,f180])).

fof(f4438,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | spl11_410 ),
    inference(resolution,[],[f4217,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4413,plain,
    ( spl11_7
    | ~ spl11_3
    | ~ spl11_422
    | ~ spl11_258
    | ~ spl11_230
    | spl11_260
    | ~ spl11_412
    | ~ spl11_16
    | spl11_413 ),
    inference(avatar_split_clause,[],[f4412,f4248,f178,f4243,f2707,f2075,f2696,f4324,f98,f117])).

fof(f4324,plain,
    ( spl11_422
  <=> r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_422])])).

fof(f4243,plain,
    ( spl11_412
  <=> m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_412])])).

fof(f4248,plain,
    ( spl11_413
  <=> r1_orders_2(sK1,sK9(sK1,sK2,sK7(sK0,sK2)),sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_413])])).

fof(f4412,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_413 ),
    inference(forward_demodulation,[],[f4329,f180])).

fof(f4329,plain,
    ( m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_413 ),
    inference(forward_demodulation,[],[f4328,f180])).

fof(f4328,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_413 ),
    inference(forward_demodulation,[],[f4320,f180])).

fof(f4320,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | spl11_413 ),
    inference(resolution,[],[f4250,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,sK9(X0,X1,X2),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4250,plain,
    ( ~ r1_orders_2(sK1,sK9(sK1,sK2,sK7(sK0,sK2)),sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | spl11_413 ),
    inference(avatar_component_clause,[],[f4248])).

fof(f4400,plain,
    ( ~ spl11_261
    | ~ spl11_260
    | ~ spl11_230
    | ~ spl11_253
    | spl11_259 ),
    inference(avatar_split_clause,[],[f3226,f2703,f2452,f2075,f2707,f2712])).

fof(f2712,plain,
    ( spl11_261
  <=> r1_orders_2(sK0,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_261])])).

fof(f2452,plain,
    ( spl11_253
  <=> ! [X1,X0] :
        ( r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_253])])).

fof(f2703,plain,
    ( spl11_259
  <=> r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_259])])).

fof(f3226,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl11_253
    | spl11_259 ),
    inference(resolution,[],[f2705,f2453])).

fof(f2453,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl11_253 ),
    inference(avatar_component_clause,[],[f2452])).

fof(f2705,plain,
    ( ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | spl11_259 ),
    inference(avatar_component_clause,[],[f2703])).

fof(f4398,plain,
    ( spl11_7
    | ~ spl11_3
    | ~ spl11_422
    | ~ spl11_257
    | ~ spl11_258
    | ~ spl11_230
    | ~ spl11_412
    | ~ spl11_16
    | spl11_413 ),
    inference(avatar_split_clause,[],[f4397,f4248,f178,f4243,f2075,f2696,f2692,f4324,f98,f117])).

fof(f4397,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_413 ),
    inference(forward_demodulation,[],[f4396,f180])).

fof(f4396,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_413 ),
    inference(forward_demodulation,[],[f4318,f180])).

fof(f4318,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | spl11_413 ),
    inference(resolution,[],[f4250,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,sK9(X0,X1,X2),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4395,plain,
    ( ~ spl11_5
    | spl11_263
    | ~ spl11_1
    | ~ spl11_407
    | ~ spl11_273
    | spl11_425 ),
    inference(avatar_split_clause,[],[f4393,f4386,f2864,f4199,f88,f2725,f107])).

fof(f107,plain,
    ( spl11_5
  <=> r1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f4386,plain,
    ( spl11_425
  <=> r2_lattice3(sK0,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_425])])).

fof(f4393,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_yellow_0(sK0,sK2)
    | spl11_425 ),
    inference(resolution,[],[f4388,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,X1,sK10(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | sK7(X0,X1) = X3
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4388,plain,
    ( ~ r2_lattice3(sK0,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | spl11_425 ),
    inference(avatar_component_clause,[],[f4386])).

fof(f4389,plain,
    ( ~ spl11_425
    | ~ spl11_412
    | ~ spl11_219
    | spl11_422 ),
    inference(avatar_split_clause,[],[f4379,f4324,f1970,f4243,f4386])).

fof(f1970,plain,
    ( spl11_219
  <=> ! [X1,X0] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_219])])).

fof(f4379,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ spl11_219
    | spl11_422 ),
    inference(resolution,[],[f4326,f1971])).

fof(f1971,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1) )
    | ~ spl11_219 ),
    inference(avatar_component_clause,[],[f1970])).

fof(f4326,plain,
    ( ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | spl11_422 ),
    inference(avatar_component_clause,[],[f4324])).

fof(f4327,plain,
    ( spl11_7
    | ~ spl11_3
    | ~ spl11_422
    | spl11_272
    | ~ spl11_258
    | ~ spl11_230
    | ~ spl11_412
    | ~ spl11_16
    | spl11_413 ),
    inference(avatar_split_clause,[],[f4322,f4248,f178,f4243,f2075,f2696,f2853,f4324,f98,f117])).

fof(f2853,plain,
    ( spl11_272
  <=> r2_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_272])])).

fof(f4322,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_413 ),
    inference(forward_demodulation,[],[f4321,f180])).

fof(f4321,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_413 ),
    inference(forward_demodulation,[],[f4319,f180])).

fof(f4319,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | spl11_413 ),
    inference(resolution,[],[f4250,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,sK9(X0,X1,X2),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4258,plain,
    ( ~ spl11_5
    | spl11_263
    | ~ spl11_1
    | ~ spl11_407
    | ~ spl11_273
    | spl11_412 ),
    inference(avatar_split_clause,[],[f4256,f4243,f2864,f4199,f88,f2725,f107])).

fof(f4256,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_yellow_0(sK0,sK2)
    | spl11_412 ),
    inference(resolution,[],[f4245,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | sK7(X0,X1) = X3
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4245,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | spl11_412 ),
    inference(avatar_component_clause,[],[f4243])).

fof(f4251,plain,
    ( ~ spl11_413
    | ~ spl11_412
    | ~ spl11_273
    | ~ spl11_241
    | spl11_408 ),
    inference(avatar_split_clause,[],[f4237,f4203,f2307,f2864,f4243,f4248])).

fof(f2307,plain,
    ( spl11_241
  <=> ! [X1,X0] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_241])])).

fof(f4203,plain,
    ( spl11_408
  <=> r1_orders_2(sK0,sK9(sK1,sK2,sK7(sK0,sK2)),sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_408])])).

fof(f4237,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_orders_2(sK1,sK9(sK1,sK2,sK7(sK0,sK2)),sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ spl11_241
    | spl11_408 ),
    inference(resolution,[],[f4205,f2308])).

fof(f2308,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X0,X1) )
    | ~ spl11_241 ),
    inference(avatar_component_clause,[],[f2307])).

fof(f4205,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1,sK2,sK7(sK0,sK2)),sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | spl11_408 ),
    inference(avatar_component_clause,[],[f4203])).

fof(f4227,plain,
    ( spl11_7
    | ~ spl11_3
    | spl11_272
    | ~ spl11_258
    | ~ spl11_230
    | ~ spl11_16
    | spl11_410 ),
    inference(avatar_split_clause,[],[f4226,f4215,f178,f2075,f2696,f2853,f98,f117])).

fof(f4226,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_410 ),
    inference(forward_demodulation,[],[f4222,f180])).

fof(f4222,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | spl11_410 ),
    inference(resolution,[],[f4217,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4206,plain,
    ( ~ spl11_407
    | spl11_263
    | ~ spl11_408
    | ~ spl11_1
    | ~ spl11_5
    | ~ spl11_273 ),
    inference(avatar_split_clause,[],[f4197,f2864,f107,f88,f4203,f2725,f4199])).

fof(f4197,plain,
    ( ~ r1_orders_2(sK0,sK9(sK1,sK2,sK7(sK0,sK2)),sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ r2_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl11_1
    | ~ spl11_5
    | ~ spl11_273 ),
    inference(resolution,[],[f4031,f109])).

fof(f109,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f4031,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,X0)
        | ~ r1_orders_2(sK0,sK9(sK1,sK2,sK7(sK0,sK2)),sK10(sK0,X0,sK9(sK1,sK2,sK7(sK0,sK2))))
        | sK7(sK0,X0) = sK9(sK1,sK2,sK7(sK0,sK2))
        | ~ r2_lattice3(sK0,X0,sK9(sK1,sK2,sK7(sK0,sK2))) )
    | ~ spl11_1
    | ~ spl11_273 ),
    inference(resolution,[],[f2866,f335])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK10(sK0,X1,X0))
        | sK7(sK0,X1) = X0
        | ~ r1_yellow_0(sK0,X1) )
    | ~ spl11_1 ),
    inference(resolution,[],[f64,f90])).

fof(f90,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ r1_orders_2(X0,X3,sK10(X0,X1,X3))
      | sK7(X0,X1) = X3
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2866,plain,
    ( m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl11_273 ),
    inference(avatar_component_clause,[],[f2864])).

fof(f3753,plain,
    ( ~ spl11_294
    | ~ spl11_276
    | ~ spl11_274
    | spl11_4
    | ~ spl11_88
    | spl11_312 ),
    inference(avatar_split_clause,[],[f3750,f3175,f703,f103,f2889,f2896,f3014])).

fof(f703,plain,
    ( spl11_88
  <=> ! [X1,X0] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | ~ r1_orders_2(sK1,sK4(sK1,X0,X1),X1)
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f3750,plain,
    ( r2_yellow_0(sK1,sK2)
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl11_88
    | spl11_312 ),
    inference(resolution,[],[f3176,f704])).

fof(f704,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | ~ r1_orders_2(sK1,sK4(sK1,X0,X1),X1)
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_88 ),
    inference(avatar_component_clause,[],[f703])).

fof(f3176,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | spl11_312 ),
    inference(avatar_component_clause,[],[f3175])).

fof(f3752,plain,
    ( ~ spl11_294
    | ~ spl11_276
    | spl11_300
    | spl11_4
    | ~ spl11_120
    | spl11_312 ),
    inference(avatar_split_clause,[],[f3749,f3175,f1009,f103,f3085,f2896,f3014])).

fof(f1009,plain,
    ( spl11_120
  <=> ! [X1,X0] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_120])])).

fof(f3749,plain,
    ( r2_yellow_0(sK1,sK2)
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl11_120
    | spl11_312 ),
    inference(resolution,[],[f3176,f1010])).

fof(f1010,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_120 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f3658,plain,
    ( spl11_4
    | ~ spl11_3
    | ~ spl11_365
    | ~ spl11_274
    | ~ spl11_276
    | ~ spl11_294
    | ~ spl11_350
    | ~ spl11_16
    | spl11_351 ),
    inference(avatar_split_clause,[],[f3657,f3471,f178,f3466,f3014,f2896,f2889,f3594,f98,f103])).

fof(f3594,plain,
    ( spl11_365
  <=> r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_365])])).

fof(f3471,plain,
    ( spl11_351
  <=> r1_orders_2(sK1,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),sK5(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_351])])).

fof(f3657,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_351 ),
    inference(forward_demodulation,[],[f3656,f180])).

fof(f3656,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_351 ),
    inference(forward_demodulation,[],[f3634,f180])).

fof(f3634,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | spl11_351 ),
    inference(resolution,[],[f3473,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3473,plain,
    ( ~ r1_orders_2(sK1,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),sK5(sK1,sK2,sK3(sK0,sK2)))
    | spl11_351 ),
    inference(avatar_component_clause,[],[f3471])).

fof(f3646,plain,
    ( spl11_4
    | ~ spl11_3
    | ~ spl11_365
    | ~ spl11_276
    | ~ spl11_294
    | spl11_300
    | ~ spl11_350
    | ~ spl11_16
    | spl11_351 ),
    inference(avatar_split_clause,[],[f3645,f3471,f178,f3466,f3085,f3014,f2896,f3594,f98,f103])).

fof(f3645,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_351 ),
    inference(forward_demodulation,[],[f3638,f180])).

fof(f3638,plain,
    ( m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_351 ),
    inference(forward_demodulation,[],[f3637,f180])).

fof(f3637,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_351 ),
    inference(forward_demodulation,[],[f3635,f180])).

fof(f3635,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | spl11_351 ),
    inference(resolution,[],[f3473,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3644,plain,
    ( ~ spl11_367
    | ~ spl11_350
    | ~ spl11_228
    | spl11_365 ),
    inference(avatar_split_clause,[],[f3641,f3594,f2066,f3466,f3603])).

fof(f3603,plain,
    ( spl11_367
  <=> r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_367])])).

fof(f2066,plain,
    ( spl11_228
  <=> ! [X1,X0] :
        ( r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_228])])).

fof(f3641,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ spl11_228
    | spl11_365 ),
    inference(resolution,[],[f3596,f2067])).

fof(f2067,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1) )
    | ~ spl11_228 ),
    inference(avatar_component_clause,[],[f2066])).

fof(f3596,plain,
    ( ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | spl11_365 ),
    inference(avatar_component_clause,[],[f3594])).

fof(f3636,plain,
    ( ~ spl11_365
    | ~ spl11_350
    | ~ spl11_311
    | spl11_351 ),
    inference(avatar_split_clause,[],[f3631,f3471,f3169,f3466,f3594])).

fof(f3169,plain,
    ( spl11_311
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,sK5(sK1,sK2,sK3(sK0,sK2)))
        | ~ r1_lattice3(sK1,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_311])])).

fof(f3631,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ spl11_311
    | spl11_351 ),
    inference(resolution,[],[f3473,f3170])).

fof(f3170,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,X0,sK5(sK1,sK2,sK3(sK0,sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,sK2,X0) )
    | ~ spl11_311 ),
    inference(avatar_component_clause,[],[f3169])).

fof(f3630,plain,
    ( ~ spl11_6
    | spl11_302
    | ~ spl11_1
    | ~ spl11_317
    | ~ spl11_312
    | spl11_367 ),
    inference(avatar_split_clause,[],[f3622,f3603,f3175,f3212,f88,f3100,f112])).

fof(f3622,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK2)
    | spl11_367 ),
    inference(resolution,[],[f3605,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,X1,sK6(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | sK3(X0,X1) = X3
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3605,plain,
    ( ~ r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | spl11_367 ),
    inference(avatar_component_clause,[],[f3603])).

fof(f3482,plain,
    ( ~ spl11_315
    | ~ spl11_312
    | ~ spl11_226
    | spl11_317 ),
    inference(avatar_split_clause,[],[f3479,f3212,f2043,f3175,f3203])).

fof(f2043,plain,
    ( spl11_226
  <=> ! [X1,X0] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_226])])).

fof(f3479,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl11_226
    | spl11_317 ),
    inference(resolution,[],[f3214,f2044])).

fof(f2044,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1) )
    | ~ spl11_226 ),
    inference(avatar_component_clause,[],[f2043])).

fof(f3214,plain,
    ( ~ r1_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | spl11_317 ),
    inference(avatar_component_clause,[],[f3212])).

fof(f3474,plain,
    ( ~ spl11_351
    | ~ spl11_312
    | ~ spl11_350
    | ~ spl11_241
    | spl11_318 ),
    inference(avatar_split_clause,[],[f3460,f3216,f2307,f3466,f3175,f3471])).

fof(f3216,plain,
    ( spl11_318
  <=> r1_orders_2(sK0,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),sK5(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_318])])).

fof(f3460,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK1,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl11_241
    | spl11_318 ),
    inference(resolution,[],[f3218,f2308])).

fof(f3218,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),sK5(sK1,sK2,sK3(sK0,sK2)))
    | spl11_318 ),
    inference(avatar_component_clause,[],[f3216])).

fof(f3458,plain,
    ( spl11_4
    | ~ spl11_3
    | spl11_305
    | ~ spl11_276
    | ~ spl11_294
    | ~ spl11_16
    | spl11_315 ),
    inference(avatar_split_clause,[],[f3457,f3203,f178,f3014,f2896,f3128,f98,f103])).

fof(f3128,plain,
    ( spl11_305
  <=> r1_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_305])])).

fof(f3457,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | r1_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_315 ),
    inference(forward_demodulation,[],[f3447,f180])).

fof(f3447,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | r1_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | spl11_315 ),
    inference(resolution,[],[f3205,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3219,plain,
    ( ~ spl11_317
    | spl11_302
    | ~ spl11_318
    | ~ spl11_1
    | ~ spl11_6
    | ~ spl11_312 ),
    inference(avatar_split_clause,[],[f3194,f3175,f112,f88,f3216,f3100,f3212])).

fof(f3194,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),sK5(sK1,sK2,sK3(sK0,sK2)))
    | sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl11_1
    | ~ spl11_6
    | ~ spl11_312 ),
    inference(resolution,[],[f3177,f2872])).

fof(f2872,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,sK2,X0),X0)
        | sK3(sK0,sK2) = X0
        | ~ r1_lattice3(sK0,sK2,X0) )
    | ~ spl11_1
    | ~ spl11_6 ),
    inference(resolution,[],[f114,f319])).

fof(f319,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ r1_orders_2(sK0,sK6(sK0,X1,X0),X0)
        | sK3(sK0,X1) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_1 ),
    inference(resolution,[],[f46,f90])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ r1_orders_2(X0,sK6(X0,X1,X3),X3)
      | sK3(X0,X1) = X3
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f114,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f3177,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl11_312 ),
    inference(avatar_component_clause,[],[f3175])).

fof(f3180,plain,
    ( spl11_4
    | ~ spl11_302
    | ~ spl11_3
    | ~ spl11_276
    | ~ spl11_294
    | ~ spl11_16
    | spl11_305 ),
    inference(avatar_split_clause,[],[f3179,f3128,f178,f3014,f2896,f98,f3100,f103])).

fof(f3179,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | sK3(sK0,sK2) != sK5(sK1,sK2,sK3(sK0,sK2))
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_305 ),
    inference(forward_demodulation,[],[f3165,f180])).

fof(f3165,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | sK3(sK0,sK2) != sK5(sK1,sK2,sK3(sK0,sK2))
    | r2_yellow_0(sK1,sK2)
    | spl11_305 ),
    inference(resolution,[],[f3130,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK5(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3130,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | spl11_305 ),
    inference(avatar_component_clause,[],[f3128])).

fof(f3178,plain,
    ( spl11_4
    | ~ spl11_3
    | ~ spl11_276
    | ~ spl11_294
    | spl11_312
    | ~ spl11_16
    | spl11_305 ),
    inference(avatar_split_clause,[],[f3173,f3128,f178,f3175,f3014,f2896,f98,f103])).

fof(f3173,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_305 ),
    inference(forward_demodulation,[],[f3172,f180])).

fof(f3172,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | r2_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_305 ),
    inference(forward_demodulation,[],[f3164,f180])).

fof(f3164,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | r2_yellow_0(sK1,sK2)
    | spl11_305 ),
    inference(resolution,[],[f3130,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3171,plain,
    ( spl11_4
    | ~ spl11_3
    | ~ spl11_276
    | ~ spl11_294
    | spl11_311
    | ~ spl11_16
    | spl11_305 ),
    inference(avatar_split_clause,[],[f3167,f3128,f178,f3169,f3014,f2896,f98,f103])).

fof(f3167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
        | ~ l1_orders_2(sK1)
        | ~ r1_lattice3(sK1,sK2,X0)
        | r1_orders_2(sK1,X0,sK5(sK1,sK2,sK3(sK0,sK2)))
        | r2_yellow_0(sK1,sK2) )
    | ~ spl11_16
    | spl11_305 ),
    inference(forward_demodulation,[],[f3166,f180])).

fof(f3166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,sK2,X0)
        | r1_orders_2(sK1,X0,sK5(sK1,sK2,sK3(sK0,sK2)))
        | r2_yellow_0(sK1,sK2) )
    | ~ spl11_16
    | spl11_305 ),
    inference(forward_demodulation,[],[f3163,f180])).

fof(f3163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,sK2,X0)
        | r1_orders_2(sK1,X0,sK5(sK1,sK2,sK3(sK0,sK2)))
        | r2_yellow_0(sK1,sK2) )
    | spl11_305 ),
    inference(resolution,[],[f3130,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK5(X0,X1,X2))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3160,plain,
    ( ~ spl11_305
    | ~ spl11_300
    | ~ spl11_226
    | spl11_307 ),
    inference(avatar_split_clause,[],[f3154,f3137,f2043,f3085,f3128])).

fof(f3137,plain,
    ( spl11_307
  <=> r1_lattice3(sK0,sK2,sK4(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_307])])).

fof(f3154,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl11_226
    | spl11_307 ),
    inference(resolution,[],[f3139,f2044])).

fof(f3139,plain,
    ( ~ r1_lattice3(sK0,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | spl11_307 ),
    inference(avatar_component_clause,[],[f3137])).

fof(f3152,plain,
    ( ~ spl11_6
    | ~ spl11_1
    | ~ spl11_307
    | ~ spl11_300
    | spl11_301 ),
    inference(avatar_split_clause,[],[f3151,f3090,f3085,f3137,f88,f112])).

fof(f3090,plain,
    ( spl11_301
  <=> r1_orders_2(sK0,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_301])])).

fof(f3151,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ r2_yellow_0(sK0,sK2)
    | spl11_301 ),
    inference(resolution,[],[f3092,f56])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK3(X0,X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3092,plain,
    ( ~ r1_orders_2(sK0,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | spl11_301 ),
    inference(avatar_component_clause,[],[f3090])).

fof(f3103,plain,
    ( ~ spl11_294
    | ~ spl11_276
    | ~ spl11_302
    | spl11_4
    | ~ spl11_55
    | spl11_300 ),
    inference(avatar_split_clause,[],[f3096,f3085,f484,f103,f3100,f2896,f3014])).

fof(f484,plain,
    ( spl11_55
  <=> ! [X1,X0] :
        ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | sK5(sK1,X0,X1) != X1
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f3096,plain,
    ( r2_yellow_0(sK1,sK2)
    | sK3(sK0,sK2) != sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl11_55
    | spl11_300 ),
    inference(resolution,[],[f3087,f485])).

fof(f485,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | sK5(sK1,X0,X1) != X1
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_55 ),
    inference(avatar_component_clause,[],[f484])).

fof(f3087,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | spl11_300 ),
    inference(avatar_component_clause,[],[f3085])).

fof(f3093,plain,
    ( ~ spl11_301
    | ~ spl11_294
    | ~ spl11_300
    | ~ spl11_243
    | spl11_274 ),
    inference(avatar_split_clause,[],[f3079,f2889,f2332,f3085,f3014,f3090])).

fof(f2332,plain,
    ( spl11_243
  <=> ! [X1,X0] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_243])])).

fof(f3079,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | ~ spl11_243
    | spl11_274 ),
    inference(resolution,[],[f2891,f2333])).

fof(f2333,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl11_243 ),
    inference(avatar_component_clause,[],[f2332])).

fof(f2891,plain,
    ( ~ r1_orders_2(sK1,sK4(sK1,sK2,sK3(sK0,sK2)),sK3(sK0,sK2))
    | spl11_274 ),
    inference(avatar_component_clause,[],[f2889])).

fof(f3046,plain,
    ( ~ spl11_6
    | ~ spl11_1
    | spl11_295 ),
    inference(avatar_split_clause,[],[f3044,f3019,f88,f112])).

fof(f3019,plain,
    ( spl11_295
  <=> r1_lattice3(sK0,sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_295])])).

fof(f3044,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r2_yellow_0(sK0,sK2)
    | spl11_295 ),
    inference(resolution,[],[f3021,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3021,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3(sK0,sK2))
    | spl11_295 ),
    inference(avatar_component_clause,[],[f3019])).

fof(f3026,plain,
    ( ~ spl11_6
    | ~ spl11_1
    | spl11_294 ),
    inference(avatar_split_clause,[],[f3024,f3014,f88,f112])).

fof(f3024,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r2_yellow_0(sK0,sK2)
    | spl11_294 ),
    inference(resolution,[],[f3016,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3016,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | spl11_294 ),
    inference(avatar_component_clause,[],[f3014])).

fof(f3022,plain,
    ( ~ spl11_295
    | ~ spl11_294
    | ~ spl11_228
    | spl11_276 ),
    inference(avatar_split_clause,[],[f3008,f2896,f2066,f3014,f3019])).

fof(f3008,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK3(sK0,sK2))
    | ~ spl11_228
    | spl11_276 ),
    inference(resolution,[],[f2898,f2067])).

fof(f2898,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3(sK0,sK2))
    | spl11_276 ),
    inference(avatar_component_clause,[],[f2896])).

fof(f2869,plain,
    ( spl11_7
    | ~ spl11_263
    | ~ spl11_3
    | ~ spl11_258
    | ~ spl11_230
    | ~ spl11_16
    | spl11_272 ),
    inference(avatar_split_clause,[],[f2868,f2853,f178,f2075,f2696,f98,f2725,f117])).

fof(f2868,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | sK7(sK0,sK2) != sK9(sK1,sK2,sK7(sK0,sK2))
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_272 ),
    inference(forward_demodulation,[],[f2860,f180])).

fof(f2860,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | sK7(sK0,sK2) != sK9(sK1,sK2,sK7(sK0,sK2))
    | r1_yellow_0(sK1,sK2)
    | spl11_272 ),
    inference(resolution,[],[f2855,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK9(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2855,plain,
    ( ~ r2_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | spl11_272 ),
    inference(avatar_component_clause,[],[f2853])).

fof(f2867,plain,
    ( spl11_7
    | ~ spl11_3
    | ~ spl11_258
    | ~ spl11_230
    | spl11_273
    | ~ spl11_16
    | spl11_272 ),
    inference(avatar_split_clause,[],[f2862,f2853,f178,f2864,f2075,f2696,f98,f117])).

fof(f2862,plain,
    ( m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_272 ),
    inference(forward_demodulation,[],[f2861,f180])).

fof(f2861,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | r1_yellow_0(sK1,sK2)
    | ~ spl11_16
    | spl11_272 ),
    inference(forward_demodulation,[],[f2859,f180])).

fof(f2859,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | r1_yellow_0(sK1,sK2)
    | spl11_272 ),
    inference(resolution,[],[f2855,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2856,plain,
    ( ~ spl11_272
    | ~ spl11_260
    | ~ spl11_215
    | spl11_270 ),
    inference(avatar_split_clause,[],[f2846,f2841,f1937,f2707,f2853])).

fof(f2841,plain,
    ( spl11_270
  <=> r2_lattice3(sK0,sK2,sK8(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_270])])).

fof(f2846,plain,
    ( ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl11_215
    | spl11_270 ),
    inference(resolution,[],[f2843,f1938])).

fof(f2843,plain,
    ( ~ r2_lattice3(sK0,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | spl11_270 ),
    inference(avatar_component_clause,[],[f2841])).

fof(f2844,plain,
    ( ~ spl11_5
    | ~ spl11_1
    | ~ spl11_270
    | ~ spl11_260
    | spl11_261 ),
    inference(avatar_split_clause,[],[f2839,f2712,f2707,f2841,f88,f107])).

fof(f2839,plain,
    ( ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK2)
    | spl11_261 ),
    inference(resolution,[],[f2714,f74])).

fof(f74,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK7(X0,X1),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X5)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2714,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | spl11_261 ),
    inference(avatar_component_clause,[],[f2712])).

fof(f2749,plain,
    ( ~ spl11_5
    | ~ spl11_1
    | spl11_265 ),
    inference(avatar_split_clause,[],[f2747,f2737,f88,f107])).

fof(f2737,plain,
    ( spl11_265
  <=> r2_lattice3(sK0,sK2,sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_265])])).

fof(f2747,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK2)
    | spl11_265 ),
    inference(resolution,[],[f2739,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK7(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2739,plain,
    ( ~ r2_lattice3(sK0,sK2,sK7(sK0,sK2))
    | spl11_265 ),
    inference(avatar_component_clause,[],[f2737])).

fof(f2740,plain,
    ( ~ spl11_265
    | ~ spl11_230
    | ~ spl11_219
    | spl11_258 ),
    inference(avatar_split_clause,[],[f2730,f2696,f1970,f2075,f2737])).

fof(f2730,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK7(sK0,sK2))
    | ~ spl11_219
    | spl11_258 ),
    inference(resolution,[],[f2698,f1971])).

fof(f2698,plain,
    ( ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | spl11_258 ),
    inference(avatar_component_clause,[],[f2696])).

fof(f2728,plain,
    ( ~ spl11_230
    | ~ spl11_258
    | ~ spl11_263
    | spl11_7
    | ~ spl11_79
    | spl11_260 ),
    inference(avatar_split_clause,[],[f2718,f2707,f644,f117,f2725,f2696,f2075])).

fof(f644,plain,
    ( spl11_79
  <=> ! [X1,X0] :
        ( m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | sK9(sK1,X0,X1) != X1
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_79])])).

fof(f2718,plain,
    ( r1_yellow_0(sK1,sK2)
    | sK7(sK0,sK2) != sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ r2_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ spl11_79
    | spl11_260 ),
    inference(resolution,[],[f2709,f645])).

fof(f645,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | sK9(sK1,X0,X1) != X1
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_79 ),
    inference(avatar_component_clause,[],[f644])).

fof(f2709,plain,
    ( ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | spl11_260 ),
    inference(avatar_component_clause,[],[f2707])).

fof(f2715,plain,
    ( ~ spl11_261
    | ~ spl11_260
    | ~ spl11_230
    | ~ spl11_243
    | spl11_257 ),
    inference(avatar_split_clause,[],[f2701,f2692,f2332,f2075,f2707,f2712])).

fof(f2701,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl11_243
    | spl11_257 ),
    inference(resolution,[],[f2694,f2333])).

fof(f2694,plain,
    ( ~ r1_orders_2(sK1,sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | spl11_257 ),
    inference(avatar_component_clause,[],[f2692])).

fof(f2710,plain,
    ( ~ spl11_259
    | ~ spl11_260
    | ~ spl11_230
    | ~ spl11_242
    | spl11_257 ),
    inference(avatar_split_clause,[],[f2700,f2692,f2321,f2075,f2707,f2703])).

fof(f2321,plain,
    ( spl11_242
  <=> ! [X3,X2] :
        ( r1_orders_2(sK1,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_242])])).

fof(f2700,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK7(sK0,sK2),sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl11_242
    | spl11_257 ),
    inference(resolution,[],[f2694,f2322])).

fof(f2322,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK1,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3) )
    | ~ spl11_242 ),
    inference(avatar_component_clause,[],[f2321])).

fof(f2454,plain,
    ( ~ spl11_1
    | spl11_253
    | ~ spl11_239 ),
    inference(avatar_split_clause,[],[f2448,f2274,f2452,f88])).

fof(f2274,plain,
    ( spl11_239
  <=> ! [X3,X5,X4] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5)
        | ~ r1_orders_2(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_orders_2(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_239])])).

fof(f2448,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_239 ),
    inference(duplicate_literal_removal,[],[f2447])).

fof(f2447,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_239 ),
    inference(equality_resolution,[],[f2275])).

fof(f2275,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5)
        | ~ r1_orders_2(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ l1_orders_2(X3) )
    | ~ spl11_239 ),
    inference(avatar_component_clause,[],[f2274])).

fof(f2334,plain,
    ( ~ spl11_1
    | spl11_243
    | ~ spl11_238 ),
    inference(avatar_split_clause,[],[f2315,f2269,f2332,f88])).

fof(f2269,plain,
    ( spl11_238
  <=> ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_orders_2(sK1,X1,X2)
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_238])])).

fof(f2315,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_238 ),
    inference(duplicate_literal_removal,[],[f2314])).

fof(f2314,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_238 ),
    inference(equality_resolution,[],[f2270])).

fof(f2270,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_orders_2(sK1,X1,X2)
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl11_238 ),
    inference(avatar_component_clause,[],[f2269])).

fof(f2330,plain,
    ( ~ spl11_10
    | spl11_242
    | ~ spl11_19
    | ~ spl11_30
    | ~ spl11_238 ),
    inference(avatar_split_clause,[],[f2329,f2269,f282,f197,f2321,f138])).

fof(f138,plain,
    ( spl11_10
  <=> l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f197,plain,
    ( spl11_19
  <=> u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f282,plain,
    ( spl11_30
  <=> u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f2329,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl11_19
    | ~ spl11_30
    | ~ spl11_238 ),
    inference(duplicate_literal_removal,[],[f2328])).

fof(f2328,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl11_19
    | ~ spl11_30
    | ~ spl11_238 ),
    inference(forward_demodulation,[],[f2327,f199])).

fof(f199,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f2327,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl11_19
    | ~ spl11_30
    | ~ spl11_238 ),
    inference(duplicate_literal_removal,[],[f2326])).

fof(f2326,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl11_19
    | ~ spl11_30
    | ~ spl11_238 ),
    inference(forward_demodulation,[],[f2325,f199])).

fof(f2325,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl11_19
    | ~ spl11_30
    | ~ spl11_238 ),
    inference(trivial_inequality_removal,[],[f2324])).

fof(f2324,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl11_19
    | ~ spl11_30
    | ~ spl11_238 ),
    inference(forward_demodulation,[],[f2313,f199])).

fof(f2313,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl11_30
    | ~ spl11_238 ),
    inference(superposition,[],[f2270,f284])).

fof(f284,plain,
    ( u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f282])).

fof(f2309,plain,
    ( ~ spl11_1
    | spl11_241
    | ~ spl11_236 ),
    inference(avatar_split_clause,[],[f2290,f2251,f2307,f88])).

fof(f2251,plain,
    ( spl11_236
  <=> ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_orders_2(X0,X1,X2)
        | ~ r1_orders_2(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_236])])).

fof(f2290,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_236 ),
    inference(duplicate_literal_removal,[],[f2289])).

fof(f2289,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_236 ),
    inference(equality_resolution,[],[f2252])).

fof(f2252,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_orders_2(X0,X1,X2)
        | ~ r1_orders_2(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl11_236 ),
    inference(avatar_component_clause,[],[f2251])).

fof(f2284,plain,
    ( ~ spl11_10
    | spl11_239
    | ~ spl11_19
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f2283,f282,f197,f2274,f138])).

fof(f2283,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_orders_2(X3,X4,X5)
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5) )
    | ~ spl11_19
    | ~ spl11_30 ),
    inference(forward_demodulation,[],[f2282,f199])).

fof(f2282,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ r1_orders_2(X3,X4,X5)
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5) )
    | ~ spl11_19
    | ~ spl11_30 ),
    inference(forward_demodulation,[],[f2281,f199])).

fof(f2281,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ r1_orders_2(X3,X4,X5)
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5) )
    | ~ spl11_19
    | ~ spl11_30 ),
    inference(forward_demodulation,[],[f2246,f199])).

fof(f2246,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ r1_orders_2(X3,X4,X5)
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5) )
    | ~ spl11_30 ),
    inference(superposition,[],[f82,f284])).

fof(f82,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X3 != X5
      | ~ r1_orders_2(X0,X4,X3)
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X2 != X4
      | X3 != X5
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f2280,plain,
    ( ~ spl11_3
    | spl11_238
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f2279,f254,f178,f2269,f98])).

fof(f254,plain,
    ( spl11_27
  <=> u1_orders_2(sK0) = u1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f2279,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f2278,f180])).

fof(f2278,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(X0,X1,X2)
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f2277,f180])).

fof(f2277,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(X0,X1,X2)
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f2245,f180])).

fof(f2245,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(X0,X1,X2)
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl11_27 ),
    inference(superposition,[],[f82,f256])).

fof(f256,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f254])).

fof(f2262,plain,
    ( ~ spl11_3
    | spl11_236
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f2261,f254,f178,f2251,f98])).

fof(f2261,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(sK1,X1,X2)
        | r1_orders_2(X0,X1,X2) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f2260,f180])).

fof(f2260,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(sK1,X1,X2)
        | r1_orders_2(X0,X1,X2) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f2259,f180])).

fof(f2259,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(sK1,X1,X2)
        | r1_orders_2(X0,X1,X2) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f2241,f180])).

fof(f2241,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(sK1,X1,X2)
        | r1_orders_2(X0,X1,X2) )
    | ~ spl11_27 ),
    inference(superposition,[],[f82,f256])).

fof(f2089,plain,
    ( ~ spl11_5
    | ~ spl11_1
    | spl11_230 ),
    inference(avatar_split_clause,[],[f2087,f2075,f88,f107])).

fof(f2087,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK2)
    | spl11_230 ),
    inference(resolution,[],[f2077,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2077,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | spl11_230 ),
    inference(avatar_component_clause,[],[f2075])).

fof(f2068,plain,
    ( ~ spl11_1
    | spl11_228
    | ~ spl11_222 ),
    inference(avatar_split_clause,[],[f2051,f2002,f2066,f88])).

fof(f2002,plain,
    ( spl11_222
  <=> ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_lattice3(sK1,X2,X1)
        | ~ r1_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_222])])).

fof(f2051,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK1,X0,X1)
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_222 ),
    inference(duplicate_literal_removal,[],[f2050])).

fof(f2050,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK1,X0,X1)
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_222 ),
    inference(equality_resolution,[],[f2003])).

fof(f2003,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_lattice3(sK1,X2,X1)
        | ~ r1_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl11_222 ),
    inference(avatar_component_clause,[],[f2002])).

fof(f2045,plain,
    ( ~ spl11_1
    | spl11_226
    | ~ spl11_220 ),
    inference(avatar_split_clause,[],[f2028,f1986,f2043,f88])).

fof(f1986,plain,
    ( spl11_220
  <=> ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_lattice3(X0,X2,X1)
        | ~ r1_lattice3(sK1,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_220])])).

fof(f2028,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_220 ),
    inference(duplicate_literal_removal,[],[f2027])).

fof(f2027,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_220 ),
    inference(equality_resolution,[],[f1987])).

fof(f1987,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_lattice3(X0,X2,X1)
        | ~ r1_lattice3(sK1,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl11_220 ),
    inference(avatar_component_clause,[],[f1986])).

fof(f2012,plain,
    ( ~ spl11_3
    | spl11_222
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f2011,f254,f178,f2002,f98])).

fof(f2011,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_lattice3(X0,X2,X1)
        | r1_lattice3(sK1,X2,X1) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f2010,f180])).

fof(f2010,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_lattice3(X0,X2,X1)
        | r1_lattice3(sK1,X2,X1) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f1980,f180])).

fof(f1980,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_lattice3(X0,X2,X1)
        | r1_lattice3(sK1,X2,X1) )
    | ~ spl11_27 ),
    inference(superposition,[],[f86,f256])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_lattice3(X0,X2,X4)
      | r1_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X3 != X4
      | ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X1,X2,X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f1996,plain,
    ( ~ spl11_3
    | spl11_220
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f1995,f254,f178,f1986,f98])).

fof(f1995,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_lattice3(sK1,X2,X1)
        | r1_lattice3(X0,X2,X1) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f1994,f180])).

fof(f1994,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_lattice3(sK1,X2,X1)
        | r1_lattice3(X0,X2,X1) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f1976,f180])).

fof(f1976,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_lattice3(sK1,X2,X1)
        | r1_lattice3(X0,X2,X1) )
    | ~ spl11_27 ),
    inference(superposition,[],[f86,f256])).

fof(f1972,plain,
    ( ~ spl11_1
    | spl11_219
    | ~ spl11_212 ),
    inference(avatar_split_clause,[],[f1955,f1903,f1970,f88])).

fof(f1903,plain,
    ( spl11_212
  <=> ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r2_lattice3(sK1,X2,X1)
        | ~ r2_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_212])])).

fof(f1955,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_212 ),
    inference(duplicate_literal_removal,[],[f1954])).

fof(f1954,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_212 ),
    inference(equality_resolution,[],[f1904])).

fof(f1904,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r2_lattice3(sK1,X2,X1)
        | ~ r2_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl11_212 ),
    inference(avatar_component_clause,[],[f1903])).

fof(f1939,plain,
    ( ~ spl11_1
    | spl11_215
    | ~ spl11_210 ),
    inference(avatar_split_clause,[],[f1922,f1887,f1937,f88])).

fof(f1887,plain,
    ( spl11_210
  <=> ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r2_lattice3(X0,X2,X1)
        | ~ r2_lattice3(sK1,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_210])])).

fof(f1922,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_210 ),
    inference(duplicate_literal_removal,[],[f1921])).

fof(f1921,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_210 ),
    inference(equality_resolution,[],[f1888])).

fof(f1888,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r2_lattice3(X0,X2,X1)
        | ~ r2_lattice3(sK1,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl11_210 ),
    inference(avatar_component_clause,[],[f1887])).

fof(f1913,plain,
    ( ~ spl11_3
    | spl11_212
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f1912,f254,f178,f1903,f98])).

fof(f1912,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X2,X1)
        | r2_lattice3(sK1,X2,X1) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f1911,f180])).

fof(f1911,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(X0,X2,X1)
        | r2_lattice3(sK1,X2,X1) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f1881,f180])).

fof(f1881,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(X0,X2,X1)
        | r2_lattice3(sK1,X2,X1) )
    | ~ spl11_27 ),
    inference(superposition,[],[f85,f256])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_lattice3(X0,X2,X4)
      | r2_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X3 != X4
      | ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X1,X2,X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1897,plain,
    ( ~ spl11_3
    | spl11_210
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f1896,f254,f178,f1887,f98])).

fof(f1896,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(sK1,X2,X1)
        | r2_lattice3(X0,X2,X1) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f1895,f180])).

fof(f1895,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(sK1,X2,X1)
        | r2_lattice3(X0,X2,X1) )
    | ~ spl11_16
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f1877,f180])).

fof(f1877,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(sK1,X2,X1)
        | r2_lattice3(X0,X2,X1) )
    | ~ spl11_27 ),
    inference(superposition,[],[f85,f256])).

fof(f1642,plain,
    ( ~ spl11_3
    | spl11_188
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f1589,f178,f1640,f98])).

fof(f1589,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | r1_yellow_0(sK1,X0) )
    | ~ spl11_16 ),
    inference(superposition,[],[f71,f180])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1128,plain,
    ( ~ spl11_3
    | spl11_131
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f1087,f178,f1126,f98])).

fof(f1087,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ r1_orders_2(sK1,X1,sK8(sK1,X0,X1))
        | ~ l1_orders_2(sK1)
        | r1_yellow_0(sK1,X0) )
    | ~ spl11_16 ),
    inference(superposition,[],[f65,f180])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK8(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1011,plain,
    ( ~ spl11_3
    | spl11_120
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f970,f178,f1009,f98])).

fof(f970,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK1)
        | r2_yellow_0(sK1,X0) )
    | ~ spl11_16 ),
    inference(superposition,[],[f53,f180])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f705,plain,
    ( ~ spl11_3
    | spl11_88
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f672,f178,f703,f98])).

fof(f672,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ r1_orders_2(sK1,sK4(sK1,X0,X1),X1)
        | ~ l1_orders_2(sK1)
        | r2_yellow_0(sK1,X0) )
    | ~ spl11_16 ),
    inference(superposition,[],[f47,f180])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f646,plain,
    ( ~ spl11_3
    | spl11_79
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f613,f178,f644,f98])).

fof(f613,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | sK9(sK1,X0,X1) != X1
        | r1_yellow_0(sK1,X0) )
    | ~ spl11_16 ),
    inference(superposition,[],[f73,f180])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK9(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f486,plain,
    ( ~ spl11_3
    | spl11_55
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f465,f178,f484,f98])).

fof(f465,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | sK5(sK1,X0,X1) != X1
        | r2_yellow_0(sK1,X0) )
    | ~ spl11_16 ),
    inference(superposition,[],[f55,f180])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK5(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f285,plain,
    ( spl11_30
    | ~ spl11_21
    | ~ spl11_26
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f276,f254,f248,f210,f282])).

fof(f210,plain,
    ( spl11_21
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f248,plain,
    ( spl11_26
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f276,plain,
    ( u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_21
    | ~ spl11_26
    | ~ spl11_27 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_21
    | ~ spl11_26
    | ~ spl11_27 ),
    inference(superposition,[],[f258,f212])).

fof(f212,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f210])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X1 )
    | ~ spl11_26
    | ~ spl11_27 ),
    inference(backward_demodulation,[],[f249,f256])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X1 )
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f248])).

fof(f257,plain,
    ( spl11_27
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f252,f248,f254])).

fof(f252,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl11_26 ),
    inference(equality_resolution,[],[f249])).

fof(f250,plain,
    ( ~ spl11_17
    | spl11_26
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f244,f191,f248,f186])).

fof(f186,plain,
    ( spl11_17
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f191,plain,
    ( spl11_18
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_orders_2(sK1) = X1 )
    | ~ spl11_18 ),
    inference(superposition,[],[f80,f193])).

fof(f193,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f213,plain,
    ( spl11_21
    | ~ spl11_11
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f203,f197,f145,f210])).

fof(f145,plain,
    ( spl11_11
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f203,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl11_11
    | ~ spl11_19 ),
    inference(backward_demodulation,[],[f147,f199])).

fof(f147,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f200,plain,
    ( spl11_19
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f195,f178,f173,f197])).

fof(f173,plain,
    ( spl11_15
  <=> u1_struct_0(sK1) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f195,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(forward_demodulation,[],[f175,f180])).

fof(f175,plain,
    ( u1_struct_0(sK1) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f194,plain,
    ( spl11_18
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f184,f178,f93,f191])).

fof(f93,plain,
    ( spl11_2
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f184,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(backward_demodulation,[],[f95,f180])).

fof(f95,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f189,plain,
    ( spl11_17
    | ~ spl11_8
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f183,f178,f124,f186])).

fof(f124,plain,
    ( spl11_8
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f183,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl11_8
    | ~ spl11_16 ),
    inference(backward_demodulation,[],[f125,f180])).

fof(f125,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f181,plain,
    ( spl11_16
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f170,f157,f178])).

fof(f157,plain,
    ( spl11_12
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f170,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl11_12 ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 )
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f176,plain,
    ( spl11_15
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f171,f157,f145,f173])).

fof(f171,plain,
    ( u1_struct_0(sK1) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK1) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(superposition,[],[f158,f147])).

fof(f159,plain,
    ( ~ spl11_8
    | spl11_12
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f151,f93,f157,f124])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | u1_struct_0(sK1) = X0 )
    | ~ spl11_2 ),
    inference(superposition,[],[f79,f95])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f148,plain,
    ( spl11_11
    | ~ spl11_10
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f143,f128,f138,f145])).

fof(f128,plain,
    ( spl11_9
  <=> v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f143,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl11_9 ),
    inference(resolution,[],[f36,f130])).

fof(f130,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f141,plain,
    ( ~ spl11_8
    | spl11_10
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f132,f93,f138,f124])).

fof(f132,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl11_2 ),
    inference(superposition,[],[f78,f95])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f136,plain,
    ( ~ spl11_3
    | spl11_8 ),
    inference(avatar_split_clause,[],[f134,f124,f98])).

fof(f134,plain,
    ( ~ l1_orders_2(sK1)
    | spl11_8 ),
    inference(resolution,[],[f35,f126])).

fof(f126,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | spl11_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f131,plain,
    ( ~ spl11_8
    | spl11_9
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f122,f93,f128,f124])).

fof(f122,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl11_2 ),
    inference(superposition,[],[f77,f95])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f121,plain,
    ( spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f28,f117,f112])).

fof(f28,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_yellow_0(X1,X2)
                & r2_yellow_0(X0,X2) )
              | ( ~ r1_yellow_0(X1,X2)
                & r1_yellow_0(X0,X2) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_yellow_0(X1,X2)
                & r2_yellow_0(X0,X2) )
              | ( ~ r1_yellow_0(X1,X2)
                & r1_yellow_0(X0,X2) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( ( r2_yellow_0(X0,X2)
                   => r2_yellow_0(X1,X2) )
                  & ( r1_yellow_0(X0,X2)
                   => r1_yellow_0(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( r2_yellow_0(X0,X2)
                 => r2_yellow_0(X1,X2) )
                & ( r1_yellow_0(X0,X2)
                 => r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_0)).

fof(f120,plain,
    ( ~ spl11_4
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f29,f117,f103])).

fof(f29,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f115,plain,
    ( spl11_6
    | spl11_5 ),
    inference(avatar_split_clause,[],[f30,f107,f112])).

fof(f30,plain,
    ( r1_yellow_0(sK0,sK2)
    | r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f110,plain,
    ( ~ spl11_4
    | spl11_5 ),
    inference(avatar_split_clause,[],[f31,f107,f103])).

fof(f31,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f32,f98])).

fof(f32,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f33,f93])).

fof(f33,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
