%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t14_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:36 EDT 2019

% Result     : Theorem 92.38s
% Output     : Refutation 92.38s
% Verified   : 
% Statistics : Number of formulae       :  559 (1424 expanded)
%              Number of leaves         :  112 ( 712 expanded)
%              Depth                    :   11
%              Number of atoms          : 2833 (6770 expanded)
%              Number of equality atoms :  196 ( 744 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122920,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f119,f126,f139,f146,f153,f154,f175,f200,f207,f225,f292,f313,f320,f332,f346,f354,f373,f438,f447,f493,f1102,f1299,f1430,f1826,f2413,f3125,f3804,f3822,f3825,f3848,f3881,f3885,f3911,f3929,f3932,f3968,f3987,f3991,f4012,f4033,f4841,f4863,f4867,f5527,f5553,f5557,f6188,f6195,f6199,f6261,f6344,f6795,f6802,f6821,f14040,f34050,f34118,f34388,f34404,f34510,f34796,f34850,f99809,f100197,f101042,f101069,f101078,f101080,f102338,f102354,f102483,f102485,f102536,f102537,f103781,f103785,f104557,f104560,f104564,f104580,f104586,f106045,f114731,f114747,f114883,f114918,f114920,f116596,f116614,f116620,f116622,f116663,f116665,f116667,f118493,f118496,f118517,f121815,f121817,f122918,f122919])).

fof(f122919,plain,
    ( ~ spl13_1413
    | spl13_1466
    | ~ spl13_1407
    | spl13_12
    | ~ spl13_514
    | spl13_3281 ),
    inference(avatar_split_clause,[],[f122916,f34505,f1824,f148,f6159,f6784,f6180])).

fof(f6180,plain,
    ( spl13_1413
  <=> ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1413])])).

fof(f6784,plain,
    ( spl13_1466
  <=> m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1466])])).

fof(f6159,plain,
    ( spl13_1407
  <=> ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1407])])).

fof(f148,plain,
    ( spl13_12
  <=> r1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f1824,plain,
    ( spl13_514
  <=> ! [X1,X0] :
        ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK1,X0,X1)
        | m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_514])])).

fof(f34505,plain,
    ( spl13_3281
  <=> ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3281])])).

fof(f122916,plain,
    ( r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_514
    | ~ spl13_3281 ),
    inference(resolution,[],[f34506,f1825])).

fof(f1825,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | ~ r2_lattice3(sK1,X0,X1)
        | m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_514 ),
    inference(avatar_component_clause,[],[f1824])).

fof(f34506,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_3281 ),
    inference(avatar_component_clause,[],[f34505])).

fof(f122918,plain,
    ( ~ spl13_1413
    | ~ spl13_1407
    | ~ spl13_1409
    | spl13_12
    | ~ spl13_390
    | spl13_3281 ),
    inference(avatar_split_clause,[],[f122917,f34505,f1428,f148,f6165,f6159,f6180])).

fof(f6165,plain,
    ( spl13_1409
  <=> ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1409])])).

fof(f1428,plain,
    ( spl13_390
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | ~ r1_orders_2(sK1,X1,sK4(sK1,X0,X1))
        | ~ r2_lattice3(sK1,X0,X1)
        | m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_390])])).

fof(f122917,plain,
    ( r1_yellow_0(sK1,sK2)
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_390
    | ~ spl13_3281 ),
    inference(resolution,[],[f34506,f1429])).

fof(f1429,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | ~ r1_orders_2(sK1,X1,sK4(sK1,X0,X1))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_390 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f121817,plain,
    ( ~ spl13_9975
    | ~ spl13_9973
    | ~ spl13_3281
    | ~ spl13_1278
    | spl13_9945 ),
    inference(avatar_split_clause,[],[f116582,f114729,f5525,f34505,f114904,f114911])).

fof(f114911,plain,
    ( spl13_9975
  <=> ~ r1_orders_2(sK1,sK5(sK1,sK2,sK3(sK0,sK2)),sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9975])])).

fof(f114904,plain,
    ( spl13_9973
  <=> ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9973])])).

fof(f5525,plain,
    ( spl13_1278
  <=> ! [X1,X0] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1278])])).

fof(f114729,plain,
    ( spl13_9945
  <=> ~ r1_orders_2(sK0,sK5(sK1,sK2,sK3(sK0,sK2)),sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9945])])).

fof(f116582,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_orders_2(sK1,sK5(sK1,sK2,sK3(sK0,sK2)),sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ spl13_1278
    | ~ spl13_9945 ),
    inference(resolution,[],[f114730,f5526])).

fof(f5526,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X0,X1) )
    | ~ spl13_1278 ),
    inference(avatar_component_clause,[],[f5525])).

fof(f114730,plain,
    ( ~ r1_orders_2(sK0,sK5(sK1,sK2,sK3(sK0,sK2)),sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ spl13_9945 ),
    inference(avatar_component_clause,[],[f114729])).

fof(f121815,plain,
    ( spl13_6
    | ~ spl13_5
    | ~ spl13_3173
    | ~ spl13_3237
    | spl13_9572
    | ~ spl13_58
    | spl13_9663 ),
    inference(avatar_split_clause,[],[f121814,f102352,f318,f99791,f34042,f33719,f121,f128])).

fof(f128,plain,
    ( spl13_6
  <=> r2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f121,plain,
    ( spl13_5
  <=> ~ l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f33719,plain,
    ( spl13_3173
  <=> ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3173])])).

fof(f34042,plain,
    ( spl13_3237
  <=> ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3237])])).

fof(f99791,plain,
    ( spl13_9572
  <=> m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9572])])).

fof(f318,plain,
    ( spl13_58
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f102352,plain,
    ( spl13_9663
  <=> ~ r1_lattice3(sK1,sK2,sK9(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9663])])).

fof(f121814,plain,
    ( m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9663 ),
    inference(forward_demodulation,[],[f121813,f319])).

fof(f319,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f318])).

fof(f121813,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9663 ),
    inference(forward_demodulation,[],[f121810,f319])).

fof(f121810,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9663 ),
    inference(resolution,[],[f102353,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',d8_yellow_0)).

fof(f102353,plain,
    ( ~ r1_lattice3(sK1,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_9663 ),
    inference(avatar_component_clause,[],[f102352])).

fof(f118517,plain,
    ( ~ spl13_9631
    | ~ spl13_9573
    | ~ spl13_998
    | spl13_9627 ),
    inference(avatar_split_clause,[],[f108568,f101040,f3966,f99794,f101056])).

fof(f101056,plain,
    ( spl13_9631
  <=> ~ r1_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9631])])).

fof(f99794,plain,
    ( spl13_9573
  <=> ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9573])])).

fof(f3966,plain,
    ( spl13_998
  <=> ! [X1,X0] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_998])])).

fof(f101040,plain,
    ( spl13_9627
  <=> ~ r1_lattice3(sK0,sK2,sK8(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9627])])).

fof(f108568,plain,
    ( ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_998
    | ~ spl13_9627 ),
    inference(resolution,[],[f101041,f3967])).

fof(f3967,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1) )
    | ~ spl13_998 ),
    inference(avatar_component_clause,[],[f3966])).

fof(f101041,plain,
    ( ~ r1_lattice3(sK0,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_9627 ),
    inference(avatar_component_clause,[],[f101040])).

fof(f118496,plain,
    ( spl13_12
    | ~ spl13_5
    | ~ spl13_9987
    | ~ spl13_1409
    | ~ spl13_1407
    | ~ spl13_1413
    | ~ spl13_9973
    | ~ spl13_58
    | spl13_9975 ),
    inference(avatar_split_clause,[],[f118495,f114911,f318,f114904,f6180,f6159,f6165,f116594,f121,f148])).

fof(f116594,plain,
    ( spl13_9987
  <=> ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9987])])).

fof(f118495,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9975 ),
    inference(forward_demodulation,[],[f118494,f319])).

fof(f118494,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9975 ),
    inference(forward_demodulation,[],[f116585,f319])).

fof(f116585,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_9975 ),
    inference(resolution,[],[f114912,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,sK5(X0,X1,X2),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',d7_yellow_0)).

fof(f114912,plain,
    ( ~ r1_orders_2(sK1,sK5(sK1,sK2,sK3(sK0,sK2)),sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ spl13_9975 ),
    inference(avatar_component_clause,[],[f114911])).

fof(f118493,plain,
    ( spl13_12
    | ~ spl13_5
    | ~ spl13_1409
    | ~ spl13_1407
    | ~ spl13_1413
    | ~ spl13_58
    | ~ spl13_1474 ),
    inference(avatar_split_clause,[],[f118492,f6816,f318,f6180,f6159,f6165,f121,f148])).

fof(f6816,plain,
    ( spl13_1474
  <=> sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1474])])).

fof(f118492,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_1474 ),
    inference(forward_demodulation,[],[f118468,f319])).

fof(f118468,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_1474 ),
    inference(trivial_inequality_removal,[],[f118464])).

fof(f118464,plain,
    ( sK3(sK0,sK2) != sK3(sK0,sK2)
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_1474 ),
    inference(superposition,[],[f64,f6817])).

fof(f6817,plain,
    ( sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ spl13_1474 ),
    inference(avatar_component_clause,[],[f6816])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f116667,plain,
    ( ~ spl13_1471
    | ~ spl13_1467
    | ~ spl13_1413
    | spl13_1469
    | ~ spl13_1994 ),
    inference(avatar_split_clause,[],[f34956,f14038,f6793,f6180,f6787,f6800])).

fof(f6800,plain,
    ( spl13_1471
  <=> ~ r1_orders_2(sK0,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1471])])).

fof(f6787,plain,
    ( spl13_1467
  <=> ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1467])])).

fof(f6793,plain,
    ( spl13_1469
  <=> ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1469])])).

fof(f14038,plain,
    ( spl13_1994
  <=> ! [X1,X0] :
        ( r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1994])])).

fof(f34956,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_1469
    | ~ spl13_1994 ),
    inference(resolution,[],[f6794,f14039])).

fof(f14039,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl13_1994 ),
    inference(avatar_component_clause,[],[f14038])).

fof(f6794,plain,
    ( ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_1469 ),
    inference(avatar_component_clause,[],[f6793])).

fof(f116665,plain,
    ( spl13_12
    | ~ spl13_5
    | ~ spl13_1409
    | ~ spl13_1407
    | ~ spl13_1413
    | ~ spl13_58
    | spl13_9949 ),
    inference(avatar_split_clause,[],[f116664,f114745,f318,f6180,f6159,f6165,f121,f148])).

fof(f114745,plain,
    ( spl13_9949
  <=> ~ r2_lattice3(sK1,sK2,sK5(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9949])])).

fof(f116664,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9949 ),
    inference(forward_demodulation,[],[f116660,f319])).

fof(f116660,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_9949 ),
    inference(resolution,[],[f114746,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114746,plain,
    ( ~ r2_lattice3(sK1,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_9949 ),
    inference(avatar_component_clause,[],[f114745])).

fof(f116663,plain,
    ( spl13_12
    | ~ spl13_5
    | ~ spl13_1407
    | ~ spl13_1413
    | spl13_1466
    | ~ spl13_58
    | spl13_9949 ),
    inference(avatar_split_clause,[],[f116662,f114745,f318,f6784,f6180,f6159,f121,f148])).

fof(f116662,plain,
    ( m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9949 ),
    inference(forward_demodulation,[],[f116661,f319])).

fof(f116661,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9949 ),
    inference(forward_demodulation,[],[f116658,f319])).

fof(f116658,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_9949 ),
    inference(resolution,[],[f114746,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f116622,plain,
    ( spl13_12
    | ~ spl13_5
    | ~ spl13_9987
    | ~ spl13_1407
    | ~ spl13_1413
    | spl13_1466
    | ~ spl13_9973
    | ~ spl13_58
    | spl13_9975 ),
    inference(avatar_split_clause,[],[f116621,f114911,f318,f114904,f6784,f6180,f6159,f116594,f121,f148])).

fof(f116621,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9975 ),
    inference(forward_demodulation,[],[f116598,f319])).

fof(f116598,plain,
    ( m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9975 ),
    inference(forward_demodulation,[],[f116597,f319])).

fof(f116597,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9975 ),
    inference(forward_demodulation,[],[f116587,f319])).

fof(f116587,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_9975 ),
    inference(resolution,[],[f114912,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,sK5(X0,X1,X2),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f116620,plain,
    ( ~ spl13_9
    | spl13_1474
    | ~ spl13_1
    | ~ spl13_9943
    | ~ spl13_3281
    | spl13_9991 ),
    inference(avatar_split_clause,[],[f116618,f116612,f34505,f114723,f107,f6816,f134])).

fof(f134,plain,
    ( spl13_9
  <=> ~ r1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f107,plain,
    ( spl13_1
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f114723,plain,
    ( spl13_9943
  <=> ~ r2_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9943])])).

fof(f116612,plain,
    ( spl13_9991
  <=> ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9991])])).

fof(f116618,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ spl13_9991 ),
    inference(resolution,[],[f116613,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_lattice3(X0,X1,sK6(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | sK3(X0,X1) = X3
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f116613,plain,
    ( ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ spl13_9991 ),
    inference(avatar_component_clause,[],[f116612])).

fof(f116614,plain,
    ( ~ spl13_9991
    | ~ spl13_9973
    | ~ spl13_984
    | spl13_9987 ),
    inference(avatar_split_clause,[],[f116600,f116594,f3883,f114904,f116612])).

fof(f3883,plain,
    ( spl13_984
  <=> ! [X1,X0] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_984])])).

fof(f116600,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ spl13_984
    | ~ spl13_9987 ),
    inference(resolution,[],[f116595,f3884])).

fof(f3884,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1) )
    | ~ spl13_984 ),
    inference(avatar_component_clause,[],[f3883])).

fof(f116595,plain,
    ( ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ spl13_9987 ),
    inference(avatar_component_clause,[],[f116594])).

fof(f116596,plain,
    ( spl13_12
    | ~ spl13_5
    | ~ spl13_9987
    | spl13_3258
    | ~ spl13_1407
    | ~ spl13_1413
    | ~ spl13_9973
    | ~ spl13_58
    | spl13_9975 ),
    inference(avatar_split_clause,[],[f116589,f114911,f318,f114904,f6180,f6159,f34399,f116594,f121,f148])).

fof(f34399,plain,
    ( spl13_3258
  <=> r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3258])])).

fof(f116589,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9975 ),
    inference(forward_demodulation,[],[f116588,f319])).

fof(f116588,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9975 ),
    inference(forward_demodulation,[],[f116586,f319])).

fof(f116586,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_9975 ),
    inference(resolution,[],[f114912,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,sK5(X0,X1,X2),X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114920,plain,
    ( spl13_12
    | ~ spl13_1475
    | ~ spl13_5
    | ~ spl13_1407
    | ~ spl13_1413
    | ~ spl13_58
    | spl13_3259 ),
    inference(avatar_split_clause,[],[f114919,f34402,f318,f6180,f6159,f121,f6819,f148])).

fof(f6819,plain,
    ( spl13_1475
  <=> sK3(sK0,sK2) != sK5(sK1,sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1475])])).

fof(f34402,plain,
    ( spl13_3259
  <=> ~ r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3259])])).

fof(f114919,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | sK3(sK0,sK2) != sK5(sK1,sK2,sK3(sK0,sK2))
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_3259 ),
    inference(forward_demodulation,[],[f34501,f319])).

fof(f34501,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | sK3(sK0,sK2) != sK5(sK1,sK2,sK3(sK0,sK2))
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_3259 ),
    inference(resolution,[],[f34403,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK5(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f34403,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_3259 ),
    inference(avatar_component_clause,[],[f34402])).

fof(f114918,plain,
    ( ~ spl13_9
    | spl13_1474
    | ~ spl13_1
    | ~ spl13_9943
    | ~ spl13_3281
    | spl13_9973 ),
    inference(avatar_split_clause,[],[f114916,f114904,f34505,f114723,f107,f6816,f134])).

fof(f114916,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ spl13_9973 ),
    inference(resolution,[],[f114905,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | sK3(X0,X1) = X3
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114905,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))),u1_struct_0(sK0))
    | ~ spl13_9973 ),
    inference(avatar_component_clause,[],[f114904])).

fof(f114883,plain,
    ( spl13_12
    | ~ spl13_5
    | spl13_3258
    | ~ spl13_1407
    | ~ spl13_1413
    | ~ spl13_58
    | spl13_9949 ),
    inference(avatar_split_clause,[],[f114882,f114745,f318,f6180,f6159,f34399,f121,f148])).

fof(f114882,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9949 ),
    inference(forward_demodulation,[],[f114878,f319])).

fof(f114878,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_9949 ),
    inference(resolution,[],[f114746,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114747,plain,
    ( ~ spl13_9949
    | ~ spl13_3281
    | ~ spl13_976
    | spl13_9943 ),
    inference(avatar_split_clause,[],[f114733,f114723,f3846,f34505,f114745])).

fof(f3846,plain,
    ( spl13_976
  <=> ! [X1,X0] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_976])])).

fof(f114733,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_976
    | ~ spl13_9943 ),
    inference(resolution,[],[f114724,f3847])).

fof(f3847,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1) )
    | ~ spl13_976 ),
    inference(avatar_component_clause,[],[f3846])).

fof(f114724,plain,
    ( ~ r2_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_9943 ),
    inference(avatar_component_clause,[],[f114723])).

fof(f114731,plain,
    ( ~ spl13_9943
    | spl13_1474
    | ~ spl13_9945
    | ~ spl13_0
    | ~ spl13_8
    | ~ spl13_3280 ),
    inference(avatar_split_clause,[],[f114718,f34508,f137,f110,f114729,f6816,f114723])).

fof(f110,plain,
    ( spl13_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f137,plain,
    ( spl13_8
  <=> r1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f34508,plain,
    ( spl13_3280
  <=> m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3280])])).

fof(f114718,plain,
    ( ~ r1_orders_2(sK0,sK5(sK1,sK2,sK3(sK0,sK2)),sK6(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2))))
    | sK3(sK0,sK2) = sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ r2_lattice3(sK0,sK2,sK5(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_0
    | ~ spl13_8
    | ~ spl13_3280 ),
    inference(resolution,[],[f108591,f138])).

fof(f138,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f108591,plain,
    ( ! [X22] :
        ( ~ r1_yellow_0(sK0,X22)
        | ~ r1_orders_2(sK0,sK5(sK1,sK2,sK3(sK0,sK2)),sK6(sK0,X22,sK5(sK1,sK2,sK3(sK0,sK2))))
        | sK3(sK0,X22) = sK5(sK1,sK2,sK3(sK0,sK2))
        | ~ r2_lattice3(sK0,X22,sK5(sK1,sK2,sK3(sK0,sK2))) )
    | ~ spl13_0
    | ~ spl13_3280 ),
    inference(resolution,[],[f34509,f635])).

fof(f635,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X7,X6)
        | ~ r1_orders_2(sK0,X6,sK6(sK0,X7,X6))
        | sK3(sK0,X7) = X6
        | ~ r1_yellow_0(sK0,X7) )
    | ~ spl13_0 ),
    inference(resolution,[],[f61,f111])).

fof(f111,plain,
    ( l1_orders_2(sK0)
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f110])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ r1_orders_2(X0,X3,sK6(X0,X1,X3))
      | sK3(X0,X1) = X3
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f34509,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_3280 ),
    inference(avatar_component_clause,[],[f34508])).

fof(f106045,plain,
    ( spl13_6
    | ~ spl13_5
    | ~ spl13_3175
    | ~ spl13_3173
    | ~ spl13_3237
    | ~ spl13_58
    | ~ spl13_9578 ),
    inference(avatar_split_clause,[],[f106044,f100192,f318,f34042,f33719,f33725,f121,f128])).

fof(f33725,plain,
    ( spl13_3175
  <=> ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3175])])).

fof(f100192,plain,
    ( spl13_9578
  <=> sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9578])])).

fof(f106044,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9578 ),
    inference(forward_demodulation,[],[f106020,f319])).

fof(f106020,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9578 ),
    inference(trivial_inequality_removal,[],[f106016])).

fof(f106016,plain,
    ( sK7(sK0,sK2) != sK7(sK0,sK2)
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9578 ),
    inference(superposition,[],[f82,f100193])).

fof(f100193,plain,
    ( sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ spl13_9578 ),
    inference(avatar_component_clause,[],[f100192])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104586,plain,
    ( ~ spl13_11
    | spl13_9578
    | ~ spl13_1
    | ~ spl13_9657
    | ~ spl13_9635
    | spl13_9725 ),
    inference(avatar_split_clause,[],[f104584,f104578,f101073,f102330,f107,f100192,f141])).

fof(f141,plain,
    ( spl13_11
  <=> ~ r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f102330,plain,
    ( spl13_9657
  <=> ~ r1_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9657])])).

fof(f101073,plain,
    ( spl13_9635
  <=> ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9635])])).

fof(f104578,plain,
    ( spl13_9725
  <=> ~ r1_lattice3(sK0,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9725])])).

fof(f104584,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK2)
    | ~ spl13_9725 ),
    inference(resolution,[],[f104579,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r1_lattice3(X0,X1,sK10(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | sK7(X0,X1) = X3
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104579,plain,
    ( ~ r1_lattice3(sK0,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ spl13_9725 ),
    inference(avatar_component_clause,[],[f104578])).

fof(f104580,plain,
    ( ~ spl13_9725
    | ~ spl13_9711
    | ~ spl13_1002
    | spl13_9721 ),
    inference(avatar_split_clause,[],[f104566,f104555,f3989,f103772,f104578])).

fof(f103772,plain,
    ( spl13_9711
  <=> ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9711])])).

fof(f3989,plain,
    ( spl13_1002
  <=> ! [X1,X0] :
        ( r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1002])])).

fof(f104555,plain,
    ( spl13_9721
  <=> ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9721])])).

fof(f104566,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ spl13_1002
    | ~ spl13_9721 ),
    inference(resolution,[],[f104556,f3990])).

fof(f3990,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1) )
    | ~ spl13_1002 ),
    inference(avatar_component_clause,[],[f3989])).

fof(f104556,plain,
    ( ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ spl13_9721 ),
    inference(avatar_component_clause,[],[f104555])).

fof(f104564,plain,
    ( spl13_6
    | ~ spl13_5
    | ~ spl13_9721
    | ~ spl13_3173
    | ~ spl13_3237
    | spl13_9572
    | ~ spl13_9711
    | ~ spl13_58
    | spl13_9713 ),
    inference(avatar_split_clause,[],[f104563,f103779,f318,f103772,f99791,f34042,f33719,f104555,f121,f128])).

fof(f103779,plain,
    ( spl13_9713
  <=> ~ r1_orders_2(sK1,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),sK9(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9713])])).

fof(f104563,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9713 ),
    inference(forward_demodulation,[],[f104562,f319])).

fof(f104562,plain,
    ( m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9713 ),
    inference(forward_demodulation,[],[f104561,f319])).

fof(f104561,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9713 ),
    inference(forward_demodulation,[],[f104550,f319])).

fof(f104550,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9713 ),
    inference(resolution,[],[f103780,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103780,plain,
    ( ~ r1_orders_2(sK1,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_9713 ),
    inference(avatar_component_clause,[],[f103779])).

fof(f104560,plain,
    ( spl13_6
    | ~ spl13_5
    | ~ spl13_9721
    | ~ spl13_3175
    | ~ spl13_3173
    | ~ spl13_3237
    | ~ spl13_9711
    | ~ spl13_58
    | spl13_9713 ),
    inference(avatar_split_clause,[],[f104559,f103779,f318,f103772,f34042,f33719,f33725,f104555,f121,f128])).

fof(f104559,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9713 ),
    inference(forward_demodulation,[],[f104558,f319])).

fof(f104558,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9713 ),
    inference(forward_demodulation,[],[f104549,f319])).

fof(f104549,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9713 ),
    inference(resolution,[],[f103780,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104557,plain,
    ( ~ spl13_9721
    | ~ spl13_9711
    | ~ spl13_9632
    | spl13_9713 ),
    inference(avatar_split_clause,[],[f104546,f103779,f101067,f103772,f104555])).

fof(f101067,plain,
    ( spl13_9632
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,sK9(sK1,sK2,sK7(sK0,sK2)))
        | ~ r1_lattice3(sK1,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9632])])).

fof(f104546,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))))
    | ~ spl13_9632
    | ~ spl13_9713 ),
    inference(resolution,[],[f103780,f101068])).

fof(f101068,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,X0,sK9(sK1,sK2,sK7(sK0,sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,sK2,X0) )
    | ~ spl13_9632 ),
    inference(avatar_component_clause,[],[f101067])).

fof(f103785,plain,
    ( ~ spl13_11
    | spl13_9578
    | ~ spl13_1
    | ~ spl13_9657
    | ~ spl13_9635
    | spl13_9711 ),
    inference(avatar_split_clause,[],[f103783,f103772,f101073,f102330,f107,f100192,f141])).

fof(f103783,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ r2_yellow_0(sK0,sK2)
    | ~ spl13_9711 ),
    inference(resolution,[],[f103773,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | sK7(X0,X1) = X3
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103773,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ spl13_9711 ),
    inference(avatar_component_clause,[],[f103772])).

fof(f103781,plain,
    ( ~ spl13_9713
    | ~ spl13_9635
    | ~ spl13_9711
    | ~ spl13_1278
    | spl13_9659 ),
    inference(avatar_split_clause,[],[f103761,f102336,f5525,f103772,f101073,f103779])).

fof(f102336,plain,
    ( spl13_9659
  <=> ~ r1_orders_2(sK0,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),sK9(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9659])])).

fof(f103761,plain,
    ( ~ m1_subset_1(sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK1,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_1278
    | ~ spl13_9659 ),
    inference(resolution,[],[f102337,f5526])).

fof(f102337,plain,
    ( ~ r1_orders_2(sK0,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_9659 ),
    inference(avatar_component_clause,[],[f102336])).

fof(f102537,plain,
    ( ~ spl13_3237
    | ~ spl13_3173
    | ~ spl13_3175
    | spl13_6
    | ~ spl13_658
    | spl13_9635 ),
    inference(avatar_split_clause,[],[f102534,f101073,f2411,f128,f33725,f33719,f34042])).

fof(f2411,plain,
    ( spl13_658
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | ~ r1_orders_2(sK1,sK8(sK1,X0,X1),X1)
        | ~ r1_lattice3(sK1,X0,X1)
        | m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_658])])).

fof(f102534,plain,
    ( r2_yellow_0(sK1,sK2)
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_658
    | ~ spl13_9635 ),
    inference(resolution,[],[f101074,f2412])).

fof(f2412,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | ~ r1_orders_2(sK1,sK8(sK1,X0,X1),X1)
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_658 ),
    inference(avatar_component_clause,[],[f2411])).

fof(f101074,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_9635 ),
    inference(avatar_component_clause,[],[f101073])).

fof(f102536,plain,
    ( ~ spl13_3237
    | spl13_9572
    | ~ spl13_3173
    | spl13_6
    | ~ spl13_842
    | spl13_9635 ),
    inference(avatar_split_clause,[],[f102533,f101073,f3123,f128,f33719,f99791,f34042])).

fof(f3123,plain,
    ( spl13_842
  <=> ! [X1,X0] :
        ( m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | ~ r1_lattice3(sK1,X0,X1)
        | m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_842])])).

fof(f102533,plain,
    ( r2_yellow_0(sK1,sK2)
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_842
    | ~ spl13_9635 ),
    inference(resolution,[],[f101074,f3124])).

fof(f3124,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | ~ r1_lattice3(sK1,X0,X1)
        | m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_842 ),
    inference(avatar_component_clause,[],[f3123])).

fof(f102485,plain,
    ( spl13_6
    | ~ spl13_5
    | ~ spl13_3175
    | ~ spl13_3173
    | ~ spl13_3237
    | ~ spl13_58
    | spl13_9663 ),
    inference(avatar_split_clause,[],[f102484,f102352,f318,f34042,f33719,f33725,f121,f128])).

fof(f102484,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9663 ),
    inference(forward_demodulation,[],[f102479,f319])).

fof(f102479,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9663 ),
    inference(resolution,[],[f102353,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102483,plain,
    ( spl13_6
    | ~ spl13_5
    | spl13_9630
    | ~ spl13_3173
    | ~ spl13_3237
    | ~ spl13_58
    | spl13_9663 ),
    inference(avatar_split_clause,[],[f102482,f102352,f318,f34042,f33719,f101053,f121,f128])).

fof(f101053,plain,
    ( spl13_9630
  <=> r1_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9630])])).

fof(f102482,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | r1_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9663 ),
    inference(forward_demodulation,[],[f102478,f319])).

fof(f102478,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | r1_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9663 ),
    inference(resolution,[],[f102353,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102354,plain,
    ( ~ spl13_9663
    | ~ spl13_9635
    | ~ spl13_998
    | spl13_9657 ),
    inference(avatar_split_clause,[],[f102340,f102330,f3966,f101073,f102352])).

fof(f102340,plain,
    ( ~ m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_998
    | ~ spl13_9657 ),
    inference(resolution,[],[f102331,f3967])).

fof(f102331,plain,
    ( ~ r1_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_9657 ),
    inference(avatar_component_clause,[],[f102330])).

fof(f102338,plain,
    ( ~ spl13_9657
    | spl13_9578
    | ~ spl13_9659
    | ~ spl13_0
    | ~ spl13_10
    | ~ spl13_9634 ),
    inference(avatar_split_clause,[],[f102325,f101076,f144,f110,f102336,f100192,f102330])).

fof(f144,plain,
    ( spl13_10
  <=> r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f101076,plain,
    ( spl13_9634
  <=> m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9634])])).

fof(f102325,plain,
    ( ~ r1_orders_2(sK0,sK10(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2))),sK9(sK1,sK2,sK7(sK0,sK2)))
    | sK7(sK0,sK2) = sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_lattice3(sK0,sK2,sK9(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_0
    | ~ spl13_10
    | ~ spl13_9634 ),
    inference(resolution,[],[f101139,f145])).

fof(f145,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f101139,plain,
    ( ! [X95] :
        ( ~ r2_yellow_0(sK0,X95)
        | ~ r1_orders_2(sK0,sK10(sK0,X95,sK9(sK1,sK2,sK7(sK0,sK2))),sK9(sK1,sK2,sK7(sK0,sK2)))
        | sK7(sK0,X95) = sK9(sK1,sK2,sK7(sK0,sK2))
        | ~ r1_lattice3(sK0,X95,sK9(sK1,sK2,sK7(sK0,sK2))) )
    | ~ spl13_0
    | ~ spl13_9634 ),
    inference(resolution,[],[f101077,f889])).

fof(f889,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X7,X6)
        | ~ r1_orders_2(sK0,sK10(sK0,X7,X6),X6)
        | sK7(sK0,X7) = X6
        | ~ r2_yellow_0(sK0,X7) )
    | ~ spl13_0 ),
    inference(resolution,[],[f79,f111])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | ~ r1_orders_2(X0,sK10(X0,X1,X3),X3)
      | sK7(X0,X1) = X3
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101077,plain,
    ( m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_9634 ),
    inference(avatar_component_clause,[],[f101076])).

fof(f101080,plain,
    ( spl13_6
    | ~ spl13_9579
    | ~ spl13_5
    | ~ spl13_3173
    | ~ spl13_3237
    | ~ spl13_58
    | spl13_9631 ),
    inference(avatar_split_clause,[],[f101079,f101056,f318,f34042,f33719,f121,f100195,f128])).

fof(f100195,plain,
    ( spl13_9579
  <=> sK7(sK0,sK2) != sK9(sK1,sK2,sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9579])])).

fof(f101079,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | sK7(sK0,sK2) != sK9(sK1,sK2,sK7(sK0,sK2))
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9631 ),
    inference(forward_demodulation,[],[f101063,f319])).

fof(f101063,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | sK7(sK0,sK2) != sK9(sK1,sK2,sK7(sK0,sK2))
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9631 ),
    inference(resolution,[],[f101057,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK9(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101057,plain,
    ( ~ r1_lattice3(sK1,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ spl13_9631 ),
    inference(avatar_component_clause,[],[f101056])).

fof(f101078,plain,
    ( spl13_6
    | ~ spl13_5
    | ~ spl13_3173
    | ~ spl13_3237
    | spl13_9634
    | ~ spl13_58
    | spl13_9631 ),
    inference(avatar_split_clause,[],[f101071,f101056,f318,f101076,f34042,f33719,f121,f128])).

fof(f101071,plain,
    ( m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9631 ),
    inference(forward_demodulation,[],[f101070,f319])).

fof(f101070,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_9631 ),
    inference(forward_demodulation,[],[f101062,f319])).

fof(f101062,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | m1_subset_1(sK9(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK1))
    | r2_yellow_0(sK1,sK2)
    | ~ spl13_9631 ),
    inference(resolution,[],[f101057,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101069,plain,
    ( spl13_6
    | ~ spl13_5
    | ~ spl13_3173
    | ~ spl13_3237
    | spl13_9632
    | ~ spl13_58
    | spl13_9631 ),
    inference(avatar_split_clause,[],[f101065,f101056,f318,f101067,f34042,f33719,f121,f128])).

fof(f101065,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
        | ~ l1_orders_2(sK1)
        | ~ r1_lattice3(sK1,sK2,X0)
        | r1_orders_2(sK1,X0,sK9(sK1,sK2,sK7(sK0,sK2)))
        | r2_yellow_0(sK1,sK2) )
    | ~ spl13_58
    | ~ spl13_9631 ),
    inference(forward_demodulation,[],[f101064,f319])).

fof(f101064,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,sK2,X0)
        | r1_orders_2(sK1,X0,sK9(sK1,sK2,sK7(sK0,sK2)))
        | r2_yellow_0(sK1,sK2) )
    | ~ spl13_58
    | ~ spl13_9631 ),
    inference(forward_demodulation,[],[f101061,f319])).

fof(f101061,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,sK2,X0)
        | r1_orders_2(sK1,X0,sK9(sK1,sK2,sK7(sK0,sK2)))
        | r2_yellow_0(sK1,sK2) )
    | ~ spl13_9631 ),
    inference(resolution,[],[f101057,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK8(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK9(X0,X1,X2))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101042,plain,
    ( ~ spl13_11
    | ~ spl13_1
    | ~ spl13_9627
    | ~ spl13_9573
    | spl13_9577 ),
    inference(avatar_split_clause,[],[f101035,f99807,f99794,f101040,f107,f141])).

fof(f99807,plain,
    ( spl13_9577
  <=> ~ r1_orders_2(sK0,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9577])])).

fof(f101035,plain,
    ( ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK8(sK1,sK2,sK7(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ spl13_9577 ),
    inference(resolution,[],[f99808,f89])).

fof(f89,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK7(X0,X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99808,plain,
    ( ~ r1_orders_2(sK0,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ spl13_9577 ),
    inference(avatar_component_clause,[],[f99807])).

fof(f100197,plain,
    ( ~ spl13_3237
    | ~ spl13_3173
    | ~ spl13_9579
    | spl13_6
    | ~ spl13_346
    | spl13_9573 ),
    inference(avatar_split_clause,[],[f100162,f99794,f1297,f128,f100195,f33719,f34042])).

fof(f1297,plain,
    ( spl13_346
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | sK9(sK1,X0,X1) != X1
        | ~ r1_lattice3(sK1,X0,X1)
        | m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_346])])).

fof(f100162,plain,
    ( r2_yellow_0(sK1,sK2)
    | sK7(sK0,sK2) != sK9(sK1,sK2,sK7(sK0,sK2))
    | ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_346
    | ~ spl13_9573 ),
    inference(resolution,[],[f99795,f1298])).

fof(f1298,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | r2_yellow_0(sK1,X0)
        | sK9(sK1,X0,X1) != X1
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_346 ),
    inference(avatar_component_clause,[],[f1297])).

fof(f99795,plain,
    ( ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_9573 ),
    inference(avatar_component_clause,[],[f99794])).

fof(f99809,plain,
    ( ~ spl13_9577
    | ~ spl13_3237
    | ~ spl13_9573
    | ~ spl13_1282
    | spl13_3175 ),
    inference(avatar_split_clause,[],[f99789,f33725,f5555,f99794,f34042,f99807])).

fof(f5555,plain,
    ( spl13_1282
  <=> ! [X1,X0] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1282])])).

fof(f99789,plain,
    ( ~ m1_subset_1(sK8(sK1,sK2,sK7(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ spl13_1282
    | ~ spl13_3175 ),
    inference(resolution,[],[f33726,f5556])).

fof(f5556,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl13_1282 ),
    inference(avatar_component_clause,[],[f5555])).

fof(f33726,plain,
    ( ~ r1_orders_2(sK1,sK8(sK1,sK2,sK7(sK0,sK2)),sK7(sK0,sK2))
    | ~ spl13_3175 ),
    inference(avatar_component_clause,[],[f33725])).

fof(f34850,plain,
    ( ~ spl13_3241
    | ~ spl13_3237
    | ~ spl13_1010
    | spl13_3239 ),
    inference(avatar_split_clause,[],[f34846,f34048,f4031,f34042,f34055])).

fof(f34055,plain,
    ( spl13_3241
  <=> ~ r1_lattice3(sK0,sK2,sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3241])])).

fof(f4031,plain,
    ( spl13_1010
  <=> ! [X1,X0] :
        ( r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1010])])).

fof(f34048,plain,
    ( spl13_3239
  <=> ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK2,sK7(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3239])])).

fof(f34846,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK7(sK0,sK2))
    | ~ spl13_1010
    | ~ spl13_3239 ),
    inference(resolution,[],[f34049,f4032])).

fof(f4032,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1) )
    | ~ spl13_1010 ),
    inference(avatar_component_clause,[],[f4031])).

fof(f34049,plain,
    ( ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK2,sK7(sK0,sK2))
    | ~ spl13_3239 ),
    inference(avatar_component_clause,[],[f34048])).

fof(f34796,plain,
    ( ~ spl13_11
    | ~ spl13_1
    | spl13_3241 ),
    inference(avatar_split_clause,[],[f34794,f34055,f107,f141])).

fof(f34794,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ spl13_3241 ),
    inference(resolution,[],[f34056,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK7(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f34056,plain,
    ( ~ r1_lattice3(sK0,sK2,sK7(sK0,sK2))
    | ~ spl13_3241 ),
    inference(avatar_component_clause,[],[f34055])).

fof(f34510,plain,
    ( spl13_12
    | ~ spl13_5
    | ~ spl13_1407
    | ~ spl13_1413
    | spl13_3280
    | ~ spl13_58
    | spl13_3259 ),
    inference(avatar_split_clause,[],[f34503,f34402,f318,f34508,f6180,f6159,f121,f148])).

fof(f34503,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_3259 ),
    inference(forward_demodulation,[],[f34502,f319])).

fof(f34502,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_58
    | ~ spl13_3259 ),
    inference(forward_demodulation,[],[f34500,f319])).

fof(f34500,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | m1_subset_1(sK5(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK1))
    | r1_yellow_0(sK1,sK2)
    | ~ spl13_3259 ),
    inference(resolution,[],[f34403,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f34404,plain,
    ( ~ spl13_3259
    | ~ spl13_1467
    | ~ spl13_976
    | spl13_3255 ),
    inference(avatar_split_clause,[],[f34390,f34386,f3846,f6787,f34402])).

fof(f34386,plain,
    ( spl13_3255
  <=> ~ r2_lattice3(sK0,sK2,sK4(sK1,sK2,sK3(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3255])])).

fof(f34390,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_976
    | ~ spl13_3255 ),
    inference(resolution,[],[f34387,f3847])).

fof(f34387,plain,
    ( ~ r2_lattice3(sK0,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_3255 ),
    inference(avatar_component_clause,[],[f34386])).

fof(f34388,plain,
    ( ~ spl13_9
    | ~ spl13_1
    | ~ spl13_3255
    | ~ spl13_1467
    | spl13_1471 ),
    inference(avatar_split_clause,[],[f34381,f6800,f6787,f34386,f107,f134])).

fof(f34381,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ spl13_1471 ),
    inference(resolution,[],[f6801,f71])).

fof(f71,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK3(X0,X1),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X5)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6801,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_1471 ),
    inference(avatar_component_clause,[],[f6800])).

fof(f34118,plain,
    ( ~ spl13_11
    | ~ spl13_1
    | spl13_3237 ),
    inference(avatar_split_clause,[],[f34116,f34042,f107,f141])).

fof(f34116,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ spl13_3237 ),
    inference(resolution,[],[f34043,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f34043,plain,
    ( ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_3237 ),
    inference(avatar_component_clause,[],[f34042])).

fof(f34050,plain,
    ( ~ spl13_3237
    | ~ spl13_3239
    | ~ spl13_1000
    | spl13_3173 ),
    inference(avatar_split_clause,[],[f34036,f33719,f3980,f34048,f34042])).

fof(f3980,plain,
    ( spl13_1000
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | r1_lattice3(sK1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1000])])).

fof(f34036,plain,
    ( ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK2,sK7(sK0,sK2))
    | ~ m1_subset_1(sK7(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_1000
    | ~ spl13_3173 ),
    inference(resolution,[],[f33720,f3981])).

fof(f3981,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK1,X2,X3)
        | ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1000 ),
    inference(avatar_component_clause,[],[f3980])).

fof(f33720,plain,
    ( ~ r1_lattice3(sK1,sK2,sK7(sK0,sK2))
    | ~ spl13_3173 ),
    inference(avatar_component_clause,[],[f33719])).

fof(f14040,plain,
    ( ~ spl13_1
    | spl13_1994
    | ~ spl13_1184 ),
    inference(avatar_split_clause,[],[f14036,f4857,f14038,f107])).

fof(f4857,plain,
    ( spl13_1184
  <=> ! [X3,X5,X4] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5)
        | ~ r1_orders_2(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1184])])).

fof(f14036,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1184 ),
    inference(duplicate_literal_removal,[],[f14035])).

fof(f14035,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1184 ),
    inference(equality_resolution,[],[f4858])).

fof(f4858,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5)
        | ~ r1_orders_2(X3,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(X3)) )
    | ~ spl13_1184 ),
    inference(avatar_component_clause,[],[f4857])).

fof(f6821,plain,
    ( ~ spl13_1413
    | ~ spl13_1407
    | ~ spl13_1475
    | spl13_12
    | ~ spl13_282
    | spl13_1467 ),
    inference(avatar_split_clause,[],[f6806,f6787,f1100,f148,f6819,f6159,f6180])).

fof(f1100,plain,
    ( spl13_282
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | sK5(sK1,X0,X1) != X1
        | ~ r2_lattice3(sK1,X0,X1)
        | m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_282])])).

fof(f6806,plain,
    ( r1_yellow_0(sK1,sK2)
    | sK3(sK0,sK2) != sK5(sK1,sK2,sK3(sK0,sK2))
    | ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_282
    | ~ spl13_1467 ),
    inference(resolution,[],[f6788,f1101])).

fof(f1101,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | r1_yellow_0(sK1,X0)
        | sK5(sK1,X0,X1) != X1
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_282 ),
    inference(avatar_component_clause,[],[f1100])).

fof(f6788,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_1467 ),
    inference(avatar_component_clause,[],[f6787])).

fof(f6802,plain,
    ( ~ spl13_1471
    | ~ spl13_1467
    | ~ spl13_1413
    | ~ spl13_1282
    | spl13_1409 ),
    inference(avatar_split_clause,[],[f6782,f6165,f5555,f6180,f6787,f6800])).

fof(f6782,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_1282
    | ~ spl13_1409 ),
    inference(resolution,[],[f6166,f5556])).

fof(f6166,plain,
    ( ~ r1_orders_2(sK1,sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ spl13_1409 ),
    inference(avatar_component_clause,[],[f6165])).

fof(f6795,plain,
    ( ~ spl13_1467
    | ~ spl13_1413
    | ~ spl13_1469
    | ~ spl13_1280
    | spl13_1409 ),
    inference(avatar_split_clause,[],[f6781,f6165,f5544,f6793,f6180,f6787])).

fof(f5544,plain,
    ( spl13_1280
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | r1_orders_2(sK1,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1280])])).

fof(f6781,plain,
    ( ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK3(sK0,sK2),sK4(sK1,sK2,sK3(sK0,sK2)))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK2,sK3(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_1280
    | ~ spl13_1409 ),
    inference(resolution,[],[f6166,f5545])).

fof(f5545,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_1280 ),
    inference(avatar_component_clause,[],[f5544])).

fof(f6344,plain,
    ( ~ spl13_1417
    | ~ spl13_1413
    | ~ spl13_1006
    | spl13_1415 ),
    inference(avatar_split_clause,[],[f6340,f6186,f4010,f6180,f6193])).

fof(f6193,plain,
    ( spl13_1417
  <=> ~ r2_lattice3(sK0,sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1417])])).

fof(f4010,plain,
    ( spl13_1006
  <=> ! [X1,X0] :
        ( r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1006])])).

fof(f6186,plain,
    ( spl13_1415
  <=> ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK2,sK3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1415])])).

fof(f6340,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK3(sK0,sK2))
    | ~ spl13_1006
    | ~ spl13_1415 ),
    inference(resolution,[],[f6187,f4011])).

fof(f4011,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1) )
    | ~ spl13_1006 ),
    inference(avatar_component_clause,[],[f4010])).

fof(f6187,plain,
    ( ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK2,sK3(sK0,sK2))
    | ~ spl13_1415 ),
    inference(avatar_component_clause,[],[f6186])).

fof(f6261,plain,
    ( ~ spl13_9
    | ~ spl13_1
    | spl13_1417 ),
    inference(avatar_split_clause,[],[f6259,f6193,f107,f134])).

fof(f6259,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ spl13_1417 ),
    inference(resolution,[],[f6194,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK3(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6194,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3(sK0,sK2))
    | ~ spl13_1417 ),
    inference(avatar_component_clause,[],[f6193])).

fof(f6199,plain,
    ( ~ spl13_9
    | ~ spl13_1
    | spl13_1413 ),
    inference(avatar_split_clause,[],[f6197,f6180,f107,f134])).

fof(f6197,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ spl13_1413 ),
    inference(resolution,[],[f6181,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6181,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_1413 ),
    inference(avatar_component_clause,[],[f6180])).

fof(f6195,plain,
    ( ~ spl13_1417
    | ~ spl13_1413
    | ~ spl13_984
    | spl13_1407 ),
    inference(avatar_split_clause,[],[f6175,f6159,f3883,f6180,f6193])).

fof(f6175,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK3(sK0,sK2))
    | ~ spl13_984
    | ~ spl13_1407 ),
    inference(resolution,[],[f6160,f3884])).

fof(f6160,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3(sK0,sK2))
    | ~ spl13_1407 ),
    inference(avatar_component_clause,[],[f6159])).

fof(f6188,plain,
    ( ~ spl13_1413
    | ~ spl13_1415
    | ~ spl13_982
    | spl13_1407 ),
    inference(avatar_split_clause,[],[f6174,f6159,f3874,f6186,f6180])).

fof(f3874,plain,
    ( spl13_982
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | r2_lattice3(sK1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_982])])).

fof(f6174,plain,
    ( ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),sK2,sK3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_982
    | ~ spl13_1407 ),
    inference(resolution,[],[f6160,f3875])).

fof(f3875,plain,
    ( ! [X2,X3] :
        ( r2_lattice3(sK1,X2,X3)
        | ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_982 ),
    inference(avatar_component_clause,[],[f3874])).

fof(f5557,plain,
    ( ~ spl13_1
    | spl13_1282
    | ~ spl13_1182 ),
    inference(avatar_split_clause,[],[f5536,f4850,f5555,f107])).

fof(f4850,plain,
    ( spl13_1182
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X2)
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1182])])).

fof(f5536,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1182 ),
    inference(duplicate_literal_removal,[],[f5535])).

fof(f5535,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK1,X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1182 ),
    inference(equality_resolution,[],[f4851])).

fof(f4851,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | r1_orders_2(sK1,X1,X2)
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl13_1182 ),
    inference(avatar_component_clause,[],[f4850])).

fof(f5553,plain,
    ( ~ spl13_25
    | spl13_1280
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_1182 ),
    inference(avatar_split_clause,[],[f5552,f4850,f491,f352,f5544,f202])).

fof(f202,plain,
    ( spl13_25
  <=> ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f352,plain,
    ( spl13_66
  <=> u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f491,plain,
    ( spl13_100
  <=> u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_100])])).

fof(f5552,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_1182 ),
    inference(duplicate_literal_removal,[],[f5551])).

fof(f5551,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_1182 ),
    inference(forward_demodulation,[],[f5550,f353])).

fof(f353,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_66 ),
    inference(avatar_component_clause,[],[f352])).

fof(f5550,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_1182 ),
    inference(duplicate_literal_removal,[],[f5549])).

fof(f5549,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_1182 ),
    inference(forward_demodulation,[],[f5548,f353])).

fof(f5548,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_1182 ),
    inference(trivial_inequality_removal,[],[f5547])).

fof(f5547,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_1182 ),
    inference(forward_demodulation,[],[f5534,f353])).

fof(f5534,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0))
        | r1_orders_2(sK1,X2,X3)
        | ~ r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) )
    | ~ spl13_100
    | ~ spl13_1182 ),
    inference(superposition,[],[f4851,f492])).

fof(f492,plain,
    ( u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_100 ),
    inference(avatar_component_clause,[],[f491])).

fof(f5527,plain,
    ( ~ spl13_1
    | spl13_1278
    | ~ spl13_1178 ),
    inference(avatar_split_clause,[],[f5506,f4828,f5525,f107])).

fof(f4828,plain,
    ( spl13_1178
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(X0,X1,X2)
        | ~ r1_orders_2(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1178])])).

fof(f5506,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1178 ),
    inference(duplicate_literal_removal,[],[f5505])).

fof(f5505,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1178 ),
    inference(equality_resolution,[],[f4829])).

fof(f4829,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | r1_orders_2(X0,X1,X2)
        | ~ r1_orders_2(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl13_1178 ),
    inference(avatar_component_clause,[],[f4828])).

fof(f4867,plain,
    ( ~ spl13_25
    | spl13_1184
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(avatar_split_clause,[],[f4866,f491,f352,f4857,f202])).

fof(f4866,plain,
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
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(forward_demodulation,[],[f4865,f353])).

fof(f4865,plain,
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
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(forward_demodulation,[],[f4864,f353])).

fof(f4864,plain,
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
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(forward_demodulation,[],[f4821,f353])).

fof(f4821,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ r1_orders_2(X3,X4,X5)
        | r1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X4,X5) )
    | ~ spl13_100 ),
    inference(superposition,[],[f100,f492])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',t1_yellow_0)).

fof(f4863,plain,
    ( ~ spl13_5
    | spl13_1182
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f4862,f445,f318,f4850,f121])).

fof(f445,plain,
    ( spl13_90
  <=> u1_orders_2(sK0) = u1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f4862,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f4861,f319])).

fof(f4861,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(X0,X1,X2)
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f4860,f319])).

fof(f4860,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(X0,X1,X2)
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f4820,f319])).

fof(f4820,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(X0,X1,X2)
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl13_90 ),
    inference(superposition,[],[f100,f446])).

fof(f446,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl13_90 ),
    inference(avatar_component_clause,[],[f445])).

fof(f4841,plain,
    ( ~ spl13_5
    | spl13_1178
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f4840,f445,f318,f4828,f121])).

fof(f4840,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(sK1,X1,X2)
        | r1_orders_2(X0,X1,X2) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f4839,f319])).

fof(f4839,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(sK1,X1,X2)
        | r1_orders_2(X0,X1,X2) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f4838,f319])).

fof(f4838,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(sK1,X1,X2)
        | r1_orders_2(X0,X1,X2) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f4816,f319])).

fof(f4816,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(sK1,X1,X2)
        | r1_orders_2(X0,X1,X2) )
    | ~ spl13_90 ),
    inference(superposition,[],[f100,f446])).

fof(f4033,plain,
    ( ~ spl13_1
    | spl13_1010
    | ~ spl13_992 ),
    inference(avatar_split_clause,[],[f4029,f3924,f4031,f107])).

fof(f3924,plain,
    ( spl13_992
  <=> ! [X3,X5,X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4)
        | ~ r1_lattice3(X3,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_992])])).

fof(f4029,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_992 ),
    inference(duplicate_literal_removal,[],[f4028])).

fof(f4028,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_992 ),
    inference(equality_resolution,[],[f3925])).

fof(f3925,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4)
        | ~ r1_lattice3(X3,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(X3) )
    | ~ spl13_992 ),
    inference(avatar_component_clause,[],[f3924])).

fof(f4012,plain,
    ( ~ spl13_1
    | spl13_1006
    | ~ spl13_972 ),
    inference(avatar_split_clause,[],[f4008,f3817,f4010,f107])).

fof(f3817,plain,
    ( spl13_972
  <=> ! [X3,X5,X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4)
        | ~ r2_lattice3(X3,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_972])])).

fof(f4008,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_972 ),
    inference(duplicate_literal_removal,[],[f4007])).

fof(f4007,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X0,X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_972 ),
    inference(equality_resolution,[],[f3818])).

fof(f3818,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4)
        | ~ r2_lattice3(X3,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(X3) )
    | ~ spl13_972 ),
    inference(avatar_component_clause,[],[f3817])).

fof(f3991,plain,
    ( ~ spl13_1
    | spl13_1002
    | ~ spl13_990 ),
    inference(avatar_split_clause,[],[f3974,f3918,f3989,f107])).

fof(f3918,plain,
    ( spl13_990
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK1,X2,X1)
        | ~ r1_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_990])])).

fof(f3974,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK1,X0,X1)
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_990 ),
    inference(duplicate_literal_removal,[],[f3973])).

fof(f3973,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK1,X0,X1)
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_990 ),
    inference(equality_resolution,[],[f3919])).

fof(f3919,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | r1_lattice3(sK1,X2,X1)
        | ~ r1_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(X0) )
    | ~ spl13_990 ),
    inference(avatar_component_clause,[],[f3918])).

fof(f3987,plain,
    ( ~ spl13_25
    | spl13_1000
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_990 ),
    inference(avatar_split_clause,[],[f3986,f3918,f491,f352,f3980,f202])).

fof(f3986,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattice3(sK1,X2,X3)
        | ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_990 ),
    inference(duplicate_literal_removal,[],[f3985])).

fof(f3985,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattice3(sK1,X2,X3)
        | ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_990 ),
    inference(forward_demodulation,[],[f3984,f353])).

fof(f3984,plain,
    ( ! [X2,X3] :
        ( r1_lattice3(sK1,X2,X3)
        | ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_990 ),
    inference(trivial_inequality_removal,[],[f3983])).

fof(f3983,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r1_lattice3(sK1,X2,X3)
        | ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_990 ),
    inference(forward_demodulation,[],[f3972,f353])).

fof(f3972,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0))
        | r1_lattice3(sK1,X2,X3)
        | ~ r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_100
    | ~ spl13_990 ),
    inference(superposition,[],[f3919,f492])).

fof(f3968,plain,
    ( ~ spl13_1
    | spl13_998
    | ~ spl13_986 ),
    inference(avatar_split_clause,[],[f3951,f3900,f3966,f107])).

fof(f3900,plain,
    ( spl13_986
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(X0,X2,X1)
        | ~ r1_lattice3(sK1,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_986])])).

fof(f3951,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_986 ),
    inference(duplicate_literal_removal,[],[f3950])).

fof(f3950,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_986 ),
    inference(equality_resolution,[],[f3901])).

fof(f3901,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | r1_lattice3(X0,X2,X1)
        | ~ r1_lattice3(sK1,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(X0) )
    | ~ spl13_986 ),
    inference(avatar_component_clause,[],[f3900])).

fof(f3932,plain,
    ( ~ spl13_25
    | spl13_992
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(avatar_split_clause,[],[f3931,f491,f352,f3924,f202])).

fof(f3931,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ r1_lattice3(X3,X5,X4)
        | r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4) )
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(forward_demodulation,[],[f3930,f353])).

fof(f3930,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ r1_lattice3(X3,X5,X4)
        | r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4) )
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(forward_demodulation,[],[f3894,f353])).

fof(f3894,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ r1_lattice3(X3,X5,X4)
        | r1_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4) )
    | ~ spl13_100 ),
    inference(superposition,[],[f104,f492])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_lattice3(X0,X2,X4)
      | r1_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X3 != X4
      | ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X1,X2,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',t2_yellow_0)).

fof(f3929,plain,
    ( ~ spl13_5
    | spl13_990
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f3928,f445,f318,f3918,f121])).

fof(f3928,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_lattice3(X0,X2,X1)
        | r1_lattice3(sK1,X2,X1) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f3927,f319])).

fof(f3927,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_lattice3(X0,X2,X1)
        | r1_lattice3(sK1,X2,X1) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f3893,f319])).

fof(f3893,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_lattice3(X0,X2,X1)
        | r1_lattice3(sK1,X2,X1) )
    | ~ spl13_90 ),
    inference(superposition,[],[f104,f446])).

fof(f3911,plain,
    ( ~ spl13_5
    | spl13_986
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f3910,f445,f318,f3900,f121])).

fof(f3910,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_lattice3(sK1,X2,X1)
        | r1_lattice3(X0,X2,X1) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f3909,f319])).

fof(f3909,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_lattice3(sK1,X2,X1)
        | r1_lattice3(X0,X2,X1) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f3889,f319])).

fof(f3889,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_lattice3(sK1,X2,X1)
        | r1_lattice3(X0,X2,X1) )
    | ~ spl13_90 ),
    inference(superposition,[],[f104,f446])).

fof(f3885,plain,
    ( ~ spl13_1
    | spl13_984
    | ~ spl13_970 ),
    inference(avatar_split_clause,[],[f3868,f3811,f3883,f107])).

fof(f3811,plain,
    ( spl13_970
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK1,X2,X1)
        | ~ r2_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_970])])).

fof(f3868,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_970 ),
    inference(duplicate_literal_removal,[],[f3867])).

fof(f3867,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_970 ),
    inference(equality_resolution,[],[f3812])).

fof(f3812,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | r2_lattice3(sK1,X2,X1)
        | ~ r2_lattice3(X0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(X0) )
    | ~ spl13_970 ),
    inference(avatar_component_clause,[],[f3811])).

fof(f3881,plain,
    ( ~ spl13_25
    | spl13_982
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_970 ),
    inference(avatar_split_clause,[],[f3880,f3811,f491,f352,f3874,f202])).

fof(f3880,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_lattice3(sK1,X2,X3)
        | ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_970 ),
    inference(duplicate_literal_removal,[],[f3879])).

fof(f3879,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_lattice3(sK1,X2,X3)
        | ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_970 ),
    inference(forward_demodulation,[],[f3878,f353])).

fof(f3878,plain,
    ( ! [X2,X3] :
        ( r2_lattice3(sK1,X2,X3)
        | ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_970 ),
    inference(trivial_inequality_removal,[],[f3877])).

fof(f3877,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | r2_lattice3(sK1,X2,X3)
        | ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_66
    | ~ spl13_100
    | ~ spl13_970 ),
    inference(forward_demodulation,[],[f3866,f353])).

fof(f3866,plain,
    ( ! [X2,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0))
        | r2_lattice3(sK1,X2,X3)
        | ~ r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) )
    | ~ spl13_100
    | ~ spl13_970 ),
    inference(superposition,[],[f3812,f492])).

fof(f3848,plain,
    ( ~ spl13_1
    | spl13_976
    | ~ spl13_966 ),
    inference(avatar_split_clause,[],[f3831,f3793,f3846,f107])).

fof(f3793,plain,
    ( spl13_966
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(X0,X2,X1)
        | ~ r2_lattice3(sK1,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_966])])).

fof(f3831,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_966 ),
    inference(duplicate_literal_removal,[],[f3830])).

fof(f3830,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_966 ),
    inference(equality_resolution,[],[f3794])).

fof(f3794,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | r2_lattice3(X0,X2,X1)
        | ~ r2_lattice3(sK1,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(X0) )
    | ~ spl13_966 ),
    inference(avatar_component_clause,[],[f3793])).

fof(f3825,plain,
    ( ~ spl13_25
    | spl13_972
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(avatar_split_clause,[],[f3824,f491,f352,f3817,f202])).

fof(f3824,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ r2_lattice3(X3,X5,X4)
        | r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4) )
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(forward_demodulation,[],[f3823,f353])).

fof(f3823,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ r2_lattice3(X3,X5,X4)
        | r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4) )
    | ~ spl13_66
    | ~ spl13_100 ),
    inference(forward_demodulation,[],[f3787,f353])).

fof(f3787,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(sK0))
        | ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
        | ~ l1_orders_2(X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
        | ~ r2_lattice3(X3,X5,X4)
        | r2_lattice3(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)),X5,X4) )
    | ~ spl13_100 ),
    inference(superposition,[],[f103,f492])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_lattice3(X0,X2,X4)
      | r2_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X3 != X4
      | ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X1,X2,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3822,plain,
    ( ~ spl13_5
    | spl13_970
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f3821,f445,f318,f3811,f121])).

fof(f3821,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(X0,X2,X1)
        | r2_lattice3(sK1,X2,X1) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f3820,f319])).

fof(f3820,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(X0,X2,X1)
        | r2_lattice3(sK1,X2,X1) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f3786,f319])).

fof(f3786,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(X0,X2,X1)
        | r2_lattice3(sK1,X2,X1) )
    | ~ spl13_90 ),
    inference(superposition,[],[f103,f446])).

fof(f3804,plain,
    ( ~ spl13_5
    | spl13_966
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f3803,f445,f318,f3793,f121])).

fof(f3803,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(sK1,X2,X1)
        | r2_lattice3(X0,X2,X1) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f3802,f319])).

fof(f3802,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(sK1,X2,X1)
        | r2_lattice3(X0,X2,X1) )
    | ~ spl13_58
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f3782,f319])).

fof(f3782,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r2_lattice3(sK1,X2,X1)
        | r2_lattice3(X0,X2,X1) )
    | ~ spl13_90 ),
    inference(superposition,[],[f103,f446])).

fof(f3125,plain,
    ( ~ spl13_5
    | spl13_842
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f3121,f318,f3123,f121])).

fof(f3121,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | r2_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f3120,f319])).

fof(f3120,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | r2_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f2974,f319])).

fof(f2974,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,X0,X1)
        | m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | r2_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(superposition,[],[f86,f319])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2413,plain,
    ( ~ spl13_5
    | spl13_658
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f2409,f318,f2411,f121])).

fof(f2409,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ r1_orders_2(sK1,sK8(sK1,X0,X1),X1)
        | ~ l1_orders_2(sK1)
        | r2_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f2287,f319])).

fof(f2287,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK9(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ r1_orders_2(sK1,sK8(sK1,X0,X1),X1)
        | ~ l1_orders_2(sK1)
        | r2_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(superposition,[],[f80,f319])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK8(X0,X1,X2),X2)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1826,plain,
    ( ~ spl13_5
    | spl13_514
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1822,f318,f1824,f121])).

fof(f1822,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | r1_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1821,f319])).

fof(f1821,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | r1_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1719,f319])).

fof(f1719,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,X0,X1)
        | m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | r1_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(superposition,[],[f68,f319])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1430,plain,
    ( ~ spl13_5
    | spl13_390
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1426,f318,f1428,f121])).

fof(f1426,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ r1_orders_2(sK1,X1,sK4(sK1,X0,X1))
        | ~ l1_orders_2(sK1)
        | r1_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1344,f319])).

fof(f1344,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ r1_orders_2(sK1,X1,sK4(sK1,X0,X1))
        | ~ l1_orders_2(sK1)
        | r1_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(superposition,[],[f62,f319])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1299,plain,
    ( ~ spl13_5
    | spl13_346
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1295,f318,f1297,f121])).

fof(f1295,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | sK9(sK1,X0,X1) != X1
        | r2_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1213,f319])).

fof(f1213,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK8(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | sK9(sK1,X0,X1) != X1
        | r2_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(superposition,[],[f88,f319])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK9(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1102,plain,
    ( ~ spl13_5
    | spl13_282
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1098,f318,f1100,f121])).

fof(f1098,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | sK5(sK1,X0,X1) != X1
        | r1_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1024,f319])).

fof(f1024,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK1)
        | sK5(sK1,X0,X1) != X1
        | r1_yellow_0(sK1,X0) )
    | ~ spl13_58 ),
    inference(superposition,[],[f70,f319])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | sK5(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f493,plain,
    ( spl13_100
    | ~ spl13_70
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f482,f445,f436,f371,f491])).

fof(f371,plain,
    ( spl13_70
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_70])])).

fof(f436,plain,
    ( spl13_88
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f482,plain,
    ( u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_70
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(trivial_inequality_removal,[],[f481])).

fof(f481,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_70
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(superposition,[],[f448,f372])).

fof(f372,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl13_70 ),
    inference(avatar_component_clause,[],[f371])).

fof(f448,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X1 )
    | ~ spl13_88
    | ~ spl13_90 ),
    inference(backward_demodulation,[],[f446,f437])).

fof(f437,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X1 )
    | ~ spl13_88 ),
    inference(avatar_component_clause,[],[f436])).

fof(f447,plain,
    ( spl13_90
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f440,f436,f445])).

fof(f440,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl13_88 ),
    inference(equality_resolution,[],[f437])).

fof(f438,plain,
    ( ~ spl13_61
    | spl13_88
    | ~ spl13_64 ),
    inference(avatar_split_clause,[],[f432,f344,f436,f327])).

fof(f327,plain,
    ( spl13_61
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_61])])).

fof(f344,plain,
    ( spl13_64
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f432,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_orders_2(sK1) = X1 )
    | ~ spl13_64 ),
    inference(superposition,[],[f96,f345])).

fof(f345,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl13_64 ),
    inference(avatar_component_clause,[],[f344])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',free_g1_orders_2)).

fof(f373,plain,
    ( spl13_70
    | ~ spl13_28
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f357,f352,f223,f371])).

fof(f223,plain,
    ( spl13_28
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f357,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl13_28
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f353,f224])).

fof(f224,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f223])).

fof(f354,plain,
    ( spl13_66
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f347,f318,f311,f352])).

fof(f311,plain,
    ( spl13_56
  <=> u1_struct_0(sK1) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f347,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_56
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f312,f319])).

fof(f312,plain,
    ( u1_struct_0(sK1) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f311])).

fof(f346,plain,
    ( spl13_64
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f325,f318,f117,f344])).

fof(f117,plain,
    ( spl13_2
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f325,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(backward_demodulation,[],[f319,f118])).

fof(f118,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f332,plain,
    ( spl13_60
    | ~ spl13_16
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f322,f318,f164,f330])).

fof(f330,plain,
    ( spl13_60
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f164,plain,
    ( spl13_16
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f322,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl13_16
    | ~ spl13_58 ),
    inference(backward_demodulation,[],[f319,f165])).

fof(f165,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f320,plain,
    ( spl13_58
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f305,f290,f318])).

fof(f290,plain,
    ( spl13_50
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f305,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl13_50 ),
    inference(equality_resolution,[],[f291])).

fof(f291,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 )
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f290])).

fof(f313,plain,
    ( spl13_56
    | ~ spl13_28
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f306,f290,f223,f311])).

fof(f306,plain,
    ( u1_struct_0(sK1) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_28
    | ~ spl13_50 ),
    inference(trivial_inequality_removal,[],[f304])).

fof(f304,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK1) = u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_28
    | ~ spl13_50 ),
    inference(superposition,[],[f291,f224])).

fof(f292,plain,
    ( ~ spl13_17
    | spl13_50
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f284,f117,f290,f167])).

fof(f167,plain,
    ( spl13_17
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | u1_struct_0(sK1) = X0 )
    | ~ spl13_2 ),
    inference(superposition,[],[f95,f118])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f225,plain,
    ( spl13_28
    | ~ spl13_25
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f218,f173,f202,f223])).

fof(f173,plain,
    ( spl13_18
  <=> v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f218,plain,
    ( ~ l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))),u1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))))
    | ~ spl13_18 ),
    inference(resolution,[],[f51,f174])).

fof(f174,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',abstractness_v1_orders_2)).

fof(f207,plain,
    ( ~ spl13_17
    | spl13_24
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f176,f117,f205,f167])).

fof(f205,plain,
    ( spl13_24
  <=> l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f176,plain,
    ( l1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_2 ),
    inference(superposition,[],[f94,f118])).

fof(f94,plain,(
    ! [X0,X1] :
      ( l1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',dt_g1_orders_2)).

fof(f200,plain,
    ( ~ spl13_5
    | spl13_17 ),
    inference(avatar_split_clause,[],[f198,f167,f121])).

fof(f198,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl13_17 ),
    inference(resolution,[],[f50,f168])).

fof(f168,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',dt_u1_orders_2)).

fof(f175,plain,
    ( ~ spl13_17
    | spl13_18
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f162,f117,f173,f167])).

fof(f162,plain,
    ( v1_orders_2(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl13_2 ),
    inference(superposition,[],[f93,f118])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_orders_2(g1_orders_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f154,plain,
    ( spl13_10
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f43,f151,f144])).

fof(f151,plain,
    ( spl13_13
  <=> ~ r1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f43,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t14_yellow_0.p',t14_yellow_0)).

fof(f153,plain,
    ( ~ spl13_7
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f44,f151,f131])).

fof(f131,plain,
    ( spl13_7
  <=> ~ r2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f44,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,
    ( spl13_10
    | spl13_8 ),
    inference(avatar_split_clause,[],[f45,f137,f144])).

fof(f45,plain,
    ( r1_yellow_0(sK0,sK2)
    | r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f139,plain,
    ( ~ spl13_7
    | spl13_8 ),
    inference(avatar_split_clause,[],[f46,f137,f131])).

fof(f46,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f126,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f47,f124])).

fof(f124,plain,
    ( spl13_4
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f47,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f48,f117])).

fof(f48,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,(
    spl13_0 ),
    inference(avatar_split_clause,[],[f49,f110])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
