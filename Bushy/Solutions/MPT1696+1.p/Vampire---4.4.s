%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t76_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  322 ( 997 expanded)
%              Number of leaves         :   53 ( 433 expanded)
%              Depth                    :   16
%              Number of atoms          : 2006 (7239 expanded)
%              Number of equality atoms :   31 ( 232 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2931,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f155,f162,f169,f203,f250,f258,f266,f489,f555,f674,f1134,f1229,f1235,f1267,f1275,f1294,f1332,f1361,f1503,f1552,f1567,f1626,f1994,f2055,f2262,f2309,f2319,f2330,f2399,f2464,f2479,f2551,f2581,f2611,f2680,f2700,f2797,f2860,f2925])).

fof(f2925,plain,
    ( ~ spl15_6
    | spl15_31
    | spl15_411
    | ~ spl15_414
    | ~ spl15_416
    | spl15_443 ),
    inference(avatar_contradiction_clause,[],[f2921])).

fof(f2921,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_411
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_443 ),
    inference(unit_resulting_resolution,[],[f168,f257,f2293,f2299,f2293,f2299,f2261,f2577,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( sK2(X0,X1,X2) != X2
                  & ! [X4] :
                      ( r1_orders_2(X0,X4,sK2(X0,X1,X2))
                      | ~ r1_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X7] :
                  ( sK4(X0,X1) = X7
                  | ( ~ r1_orders_2(X0,sK5(X0,X1,X7),X7)
                    & r1_lattice3(X0,X1,sK5(X0,X1,X7))
                    & m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X7)
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X9] :
                  ( r1_orders_2(X0,X9,sK4(X0,X1))
                  | ~ r1_lattice3(X0,X1,X9)
                  | ~ m1_subset_1(X9,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK4(X0,X1))
              & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f60,f64,f63,f62,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK2(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,X4,sK2(X0,X1,X2))
            | ~ r1_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X5,X2)
          & r1_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( X6 = X7
              | ? [X8] :
                  ( ~ r1_orders_2(X0,X8,X7)
                  & r1_lattice3(X0,X1,X8)
                  & m1_subset_1(X8,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X9,X6)
              | ~ r1_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ! [X7] :
            ( sK4(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X8,X7)
                & r1_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,X9,sK4(X0,X1))
            | ~ r1_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X8,X7)
          & r1_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X7),X7)
        & r1_lattice3(X0,X1,sK5(X0,X1,X7))
        & m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X6] :
                ( ! [X7] :
                    ( X6 = X7
                    | ? [X8] :
                        ( ~ r1_orders_2(X0,X8,X7)
                        & r1_lattice3(X0,X1,X8)
                        & m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ r1_lattice3(X0,X1,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                & ! [X9] :
                    ( r1_orders_2(X0,X9,X6)
                    | ~ r1_lattice3(X0,X1,X9)
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X6)
                & m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
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
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t76_waybel_0.p',d8_yellow_0)).

fof(f2577,plain,
    ( ~ r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_443 ),
    inference(avatar_component_clause,[],[f2576])).

fof(f2576,plain,
    ( spl15_443
  <=> ~ r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_443])])).

fof(f2261,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_411 ),
    inference(avatar_component_clause,[],[f2260])).

fof(f2260,plain,
    ( spl15_411
  <=> ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_411])])).

fof(f2299,plain,
    ( r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ spl15_416 ),
    inference(avatar_component_clause,[],[f2298])).

fof(f2298,plain,
    ( spl15_416
  <=> r1_lattice3(sK0,sK1,sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_416])])).

fof(f2293,plain,
    ( m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_414 ),
    inference(avatar_component_clause,[],[f2292])).

fof(f2292,plain,
    ( spl15_414
  <=> m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_414])])).

fof(f257,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ spl15_31 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl15_31
  <=> ~ r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_31])])).

fof(f168,plain,
    ( l1_orders_2(sK0)
    | ~ spl15_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl15_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f2860,plain,
    ( spl15_428
    | ~ spl15_6
    | spl15_31
    | spl15_377
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(avatar_split_clause,[],[f2806,f2298,f2292,f2050,f256,f167,f2462])).

fof(f2462,plain,
    ( spl15_428
  <=> r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_428])])).

fof(f2050,plain,
    ( spl15_377
  <=> ~ r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_377])])).

fof(f2806,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_377
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2805,f168])).

fof(f2805,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_377
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2804,f2293])).

fof(f2804,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_377
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2803,f2299])).

fof(f2803,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_377 ),
    inference(subsumption_resolution,[],[f2801,f257])).

fof(f2801,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_377 ),
    inference(resolution,[],[f2051,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f2051,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_377 ),
    inference(avatar_component_clause,[],[f2050])).

fof(f2797,plain,
    ( ~ spl15_6
    | spl15_31
    | spl15_411
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(avatar_contradiction_clause,[],[f2796])).

fof(f2796,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_411
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2795,f168])).

fof(f2795,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_411
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2794,f2293])).

fof(f2794,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_411
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2793,f2299])).

fof(f2793,plain,
    ( ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_411
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2792,f257])).

fof(f2792,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_411
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2785,f2610])).

fof(f2610,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ spl15_446 ),
    inference(avatar_component_clause,[],[f2609])).

fof(f2609,plain,
    ( spl15_446
  <=> sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_446])])).

fof(f2785,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) != sK9(sK0,sK1)
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_411 ),
    inference(resolution,[],[f2261,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | sK2(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f2700,plain,
    ( ~ spl15_6
    | spl15_31
    | spl15_377
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(avatar_contradiction_clause,[],[f2697])).

fof(f2697,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_377
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(unit_resulting_resolution,[],[f168,f257,f2293,f2299,f2610,f2051,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f2680,plain,
    ( ~ spl15_6
    | spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(avatar_contradiction_clause,[],[f2679])).

fof(f2679,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2678,f168])).

fof(f2678,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2677,f2293])).

fof(f2677,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_416
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2676,f2299])).

fof(f2676,plain,
    ( ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2675,f2255])).

fof(f2255,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_408 ),
    inference(avatar_component_clause,[],[f2254])).

fof(f2254,plain,
    ( spl15_408
  <=> r1_orders_2(sK0,sK3(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_408])])).

fof(f2675,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_446 ),
    inference(subsumption_resolution,[],[f2657,f257])).

fof(f2657,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK3(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_446 ),
    inference(trivial_inequality_removal,[],[f2654])).

fof(f2654,plain,
    ( sK9(sK0,sK1) != sK9(sK0,sK1)
    | r2_yellow_0(sK0,sK1)
    | ~ r1_orders_2(sK0,sK3(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_446 ),
    inference(superposition,[],[f110,f2610])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f2611,plain,
    ( spl15_446
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_414
    | ~ spl15_418
    | ~ spl15_424
    | ~ spl15_442 ),
    inference(avatar_split_clause,[],[f2591,f2579,f2397,f2307,f2292,f167,f160,f2609])).

fof(f160,plain,
    ( spl15_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f2307,plain,
    ( spl15_418
  <=> m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_418])])).

fof(f2397,plain,
    ( spl15_424
  <=> r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_424])])).

fof(f2579,plain,
    ( spl15_442
  <=> r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_442])])).

fof(f2591,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ spl15_4
    | ~ spl15_6
    | ~ spl15_414
    | ~ spl15_418
    | ~ spl15_424
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f2590,f161])).

fof(f161,plain,
    ( v5_orders_2(sK0)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f160])).

fof(f2590,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ v5_orders_2(sK0)
    | ~ spl15_6
    | ~ spl15_414
    | ~ spl15_418
    | ~ spl15_424
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f2589,f168])).

fof(f2589,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_414
    | ~ spl15_418
    | ~ spl15_424
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f2588,f2308])).

fof(f2308,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl15_418 ),
    inference(avatar_component_clause,[],[f2307])).

fof(f2588,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_414
    | ~ spl15_424
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f2587,f2293])).

fof(f2587,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_424
    | ~ spl15_442 ),
    inference(subsumption_resolution,[],[f2586,f2398])).

fof(f2398,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_424 ),
    inference(avatar_component_clause,[],[f2397])).

fof(f2586,plain,
    ( sK2(sK0,sK1,sK9(sK0,sK1)) = sK9(sK0,sK1)
    | ~ r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl15_442 ),
    inference(resolution,[],[f2580,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t76_waybel_0.p',t25_orders_2)).

fof(f2580,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_442 ),
    inference(avatar_component_clause,[],[f2579])).

fof(f2581,plain,
    ( spl15_442
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | ~ spl15_374
    | ~ spl15_414 ),
    inference(avatar_split_clause,[],[f2574,f2292,f2047,f264,f201,f192,f167,f153,f146,f2579])).

fof(f146,plain,
    ( spl15_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f153,plain,
    ( spl15_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f192,plain,
    ( spl15_14
  <=> v25_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f201,plain,
    ( spl15_17
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f264,plain,
    ( spl15_32
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f2047,plain,
    ( spl15_374
  <=> ! [X3] :
        ( r1_orders_2(sK0,X3,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_374])])).

fof(f2574,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_374
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f2573,f147])).

fof(f147,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f146])).

fof(f2573,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_374
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f2572,f154])).

fof(f154,plain,
    ( v3_orders_2(sK0)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f153])).

fof(f2572,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_374
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f2571,f168])).

fof(f2571,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_374
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f2570,f193])).

fof(f193,plain,
    ( v25_waybel_0(sK0)
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f192])).

fof(f2570,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_374
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f2569,f202])).

fof(f202,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f201])).

fof(f2569,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_32
    | ~ spl15_374
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f2568,f265])).

fof(f265,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_32 ),
    inference(avatar_component_clause,[],[f264])).

fof(f2568,plain,
    ( r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_374
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f2559,f2293])).

fof(f2559,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK9(sK0,sK1),sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_374 ),
    inference(resolution,[],[f2048,f115])).

fof(f115,plain,(
    ! [X4,X0] :
      ( r1_lattice3(X0,X4,sK9(X0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X4)
      | ~ v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ( ! [X2] :
                ( ( ~ r1_orders_2(X0,sK8(X0,X2),X2)
                  & r1_lattice3(X0,sK7(X0),sK8(X0,X2))
                  & m1_subset_1(sK8(X0,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,sK7(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(sK7(X0)) ) )
        & ( ! [X4] :
              ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,sK9(X0,X4))
                    | ~ r1_lattice3(X0,X4,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_lattice3(X0,X4,sK9(X0,X4))
                & m1_subset_1(sK9(X0,X4),u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X4) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f69,f72,f71,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,X3,X2)
                & r1_lattice3(X0,sK7(X0),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,sK7(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK8(X0,X2),X2)
        & r1_lattice3(X0,X1,sK8(X0,X2))
        & m1_subset_1(sK8(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X6,X5)
              | ~ r1_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r1_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,X6,sK9(X0,X4))
            | ~ r1_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r1_lattice3(X0,X4,sK9(X0,X4))
        & m1_subset_1(sK9(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X2)
                      & r1_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( ! [X6] :
                      ( r1_orders_2(X0,X6,X5)
                      | ~ r1_lattice3(X0,X4,X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X4,X5)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X4) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X2)
                      & r1_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( r1_orders_2(X0,X3,X2)
                      | ~ r1_lattice3(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X1) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t76_waybel_0.p',d40_waybel_0)).

fof(f2048,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK2(sK0,sK1,sK9(sK0,sK1))) )
    | ~ spl15_374 ),
    inference(avatar_component_clause,[],[f2047])).

fof(f2551,plain,
    ( spl15_374
    | ~ spl15_6
    | spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(avatar_split_clause,[],[f2445,f2298,f2292,f2254,f256,f167,f2047])).

fof(f2445,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2444,f168])).

fof(f2444,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2443,f2293])).

fof(f2443,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2442,f2299])).

fof(f2442,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_31
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f2438,f257])).

fof(f2438,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK1)
        | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
        | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_408 ),
    inference(resolution,[],[f2255,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f2479,plain,
    ( spl15_424
    | ~ spl15_252
    | ~ spl15_418
    | ~ spl15_428 ),
    inference(avatar_split_clause,[],[f2470,f2462,f2307,f1359,f2397])).

fof(f1359,plain,
    ( spl15_252
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X3)
        | r1_orders_2(sK0,X3,sK9(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_252])])).

fof(f2470,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_252
    | ~ spl15_418
    | ~ spl15_428 ),
    inference(subsumption_resolution,[],[f2467,f2308])).

fof(f2467,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_252
    | ~ spl15_428 ),
    inference(resolution,[],[f2463,f1360])).

fof(f1360,plain,
    ( ! [X3] :
        ( ~ r1_lattice3(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK9(sK0,sK1)) )
    | ~ spl15_252 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f2463,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_428 ),
    inference(avatar_component_clause,[],[f2462])).

fof(f2464,plain,
    ( spl15_428
    | ~ spl15_6
    | spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(avatar_split_clause,[],[f2449,f2298,f2292,f2254,f256,f167,f2462])).

fof(f2449,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2448,f168])).

fof(f2448,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_414
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2447,f2293])).

fof(f2447,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_408
    | ~ spl15_416 ),
    inference(subsumption_resolution,[],[f2446,f2299])).

fof(f2446,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_408 ),
    inference(subsumption_resolution,[],[f2439,f257])).

fof(f2439,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK9(sK0,sK1)))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_408 ),
    inference(resolution,[],[f2255,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f2399,plain,
    ( spl15_424
    | ~ spl15_274
    | spl15_411
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_418 ),
    inference(avatar_split_clause,[],[f2350,f2307,f2298,f2292,f2260,f1550,f2397])).

fof(f1550,plain,
    ( spl15_274
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_274])])).

fof(f2350,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_274
    | ~ spl15_411
    | ~ spl15_414
    | ~ spl15_416
    | ~ spl15_418 ),
    inference(subsumption_resolution,[],[f2349,f2293])).

fof(f2349,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_274
    | ~ spl15_411
    | ~ spl15_416
    | ~ spl15_418 ),
    inference(subsumption_resolution,[],[f2348,f2299])).

fof(f2348,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_274
    | ~ spl15_411
    | ~ spl15_418 ),
    inference(subsumption_resolution,[],[f2338,f2261])).

fof(f2338,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_274
    | ~ spl15_418 ),
    inference(resolution,[],[f2308,f1551])).

fof(f1551,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_274 ),
    inference(avatar_component_clause,[],[f1550])).

fof(f2330,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | spl15_417 ),
    inference(avatar_contradiction_clause,[],[f2329])).

fof(f2329,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_417 ),
    inference(subsumption_resolution,[],[f2328,f147])).

fof(f2328,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_417 ),
    inference(subsumption_resolution,[],[f2327,f154])).

fof(f2327,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_417 ),
    inference(subsumption_resolution,[],[f2326,f168])).

fof(f2326,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_417 ),
    inference(subsumption_resolution,[],[f2325,f193])).

fof(f2325,plain,
    ( ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_417 ),
    inference(subsumption_resolution,[],[f2324,f202])).

fof(f2324,plain,
    ( v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_32
    | ~ spl15_417 ),
    inference(subsumption_resolution,[],[f2322,f265])).

fof(f2322,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_417 ),
    inference(resolution,[],[f2302,f115])).

fof(f2302,plain,
    ( ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ spl15_417 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f2301,plain,
    ( spl15_417
  <=> ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_417])])).

fof(f2319,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | spl15_17
    | ~ spl15_32
    | spl15_415 ),
    inference(avatar_contradiction_clause,[],[f2318])).

fof(f2318,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_415 ),
    inference(subsumption_resolution,[],[f2317,f147])).

fof(f2317,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_415 ),
    inference(subsumption_resolution,[],[f2316,f154])).

fof(f2316,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_415 ),
    inference(subsumption_resolution,[],[f2315,f168])).

fof(f2315,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_14
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_415 ),
    inference(subsumption_resolution,[],[f2314,f193])).

fof(f2314,plain,
    ( ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_415 ),
    inference(subsumption_resolution,[],[f2313,f202])).

fof(f2313,plain,
    ( v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_32
    | ~ spl15_415 ),
    inference(subsumption_resolution,[],[f2311,f265])).

fof(f2311,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_415 ),
    inference(resolution,[],[f2296,f114])).

fof(f114,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK9(X0,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X4)
      | ~ v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f2296,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_415 ),
    inference(avatar_component_clause,[],[f2295])).

fof(f2295,plain,
    ( spl15_415
  <=> ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_415])])).

fof(f2309,plain,
    ( ~ spl15_415
    | ~ spl15_417
    | spl15_418
    | ~ spl15_6
    | spl15_31
    | ~ spl15_362 ),
    inference(avatar_split_clause,[],[f2036,f1992,f256,f167,f2307,f2301,f2295])).

fof(f1992,plain,
    ( spl15_362
  <=> ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_362])])).

fof(f2036,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_362 ),
    inference(subsumption_resolution,[],[f2035,f168])).

fof(f2035,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_31
    | ~ spl15_362 ),
    inference(subsumption_resolution,[],[f2028,f257])).

fof(f2028,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl15_362 ),
    inference(duplicate_literal_removal,[],[f2026])).

fof(f2026,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1))
    | ~ m1_subset_1(sK9(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_362 ),
    inference(resolution,[],[f1993,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1993,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_362 ),
    inference(avatar_component_clause,[],[f1992])).

fof(f2262,plain,
    ( spl15_408
    | ~ spl15_411
    | ~ spl15_252
    | ~ spl15_376 ),
    inference(avatar_split_clause,[],[f2150,f2053,f1359,f2260,f2254])).

fof(f2053,plain,
    ( spl15_376
  <=> r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_376])])).

fof(f2150,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK9(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK1,sK9(sK0,sK1)),sK9(sK0,sK1))
    | ~ spl15_252
    | ~ spl15_376 ),
    inference(resolution,[],[f2054,f1360])).

fof(f2054,plain,
    ( r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
    | ~ spl15_376 ),
    inference(avatar_component_clause,[],[f2053])).

fof(f2055,plain,
    ( spl15_374
    | spl15_376
    | spl15_17
    | spl15_31
    | ~ spl15_32
    | ~ spl15_296 ),
    inference(avatar_split_clause,[],[f1657,f1624,f264,f256,f201,f2053,f2047])).

fof(f1624,plain,
    ( spl15_296
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,sK9(sK0,X1)))
        | ~ r1_lattice3(sK0,X1,X0)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_296])])).

fof(f1657,plain,
    ( ! [X3] :
        ( r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,X3,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl15_17
    | ~ spl15_31
    | ~ spl15_32
    | ~ spl15_296 ),
    inference(subsumption_resolution,[],[f1656,f202])).

fof(f1656,plain,
    ( ! [X3] :
        ( r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,X3,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v1_xboole_0(sK1) )
    | ~ spl15_31
    | ~ spl15_32
    | ~ spl15_296 ),
    inference(subsumption_resolution,[],[f1650,f257])).

fof(f1650,plain,
    ( ! [X3] :
        ( r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK9(sK0,sK1)))
        | r1_orders_2(sK0,X3,sK2(sK0,sK1,sK9(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK1,X3)
        | r2_yellow_0(sK0,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v1_xboole_0(sK1) )
    | ~ spl15_32
    | ~ spl15_296 ),
    inference(resolution,[],[f1625,f265])).

fof(f1625,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,sK9(sK0,X1)))
        | ~ r1_lattice3(sK0,X1,X0)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(X1) )
    | ~ spl15_296 ),
    inference(avatar_component_clause,[],[f1624])).

fof(f1994,plain,
    ( spl15_362
    | ~ spl15_6
    | spl15_31
    | ~ spl15_280 ),
    inference(avatar_split_clause,[],[f1595,f1565,f256,f167,f1992])).

fof(f1565,plain,
    ( spl15_280
  <=> ! [X2] :
        ( ~ m1_subset_1(sK3(sK0,sK1,X2),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1,X2),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_280])])).

fof(f1595,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_280 ),
    inference(subsumption_resolution,[],[f1594,f168])).

fof(f1594,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_31
    | ~ spl15_280 ),
    inference(subsumption_resolution,[],[f1593,f257])).

fof(f1593,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl15_280 ),
    inference(duplicate_literal_removal,[],[f1590])).

fof(f1590,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK1)
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_280 ),
    inference(resolution,[],[f1566,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1566,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(sK0,sK1,X2),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1,X2),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl15_280 ),
    inference(avatar_component_clause,[],[f1565])).

fof(f1626,plain,
    ( spl15_296
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_268 ),
    inference(avatar_split_clause,[],[f1512,f1501,f192,f167,f153,f146,f1624])).

fof(f1501,plain,
    ( spl15_268
  <=> ! [X11,X12] :
        ( ~ r1_lattice3(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,X11,sK3(sK0,X11,sK9(sK0,X11)))
        | r1_orders_2(sK0,X12,sK2(sK0,X11,sK9(sK0,X11)))
        | ~ m1_subset_1(sK9(sK0,X11),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_268])])).

fof(f1512,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,sK9(sK0,X1)))
        | ~ r1_lattice3(sK0,X1,X0)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_268 ),
    inference(subsumption_resolution,[],[f1511,f147])).

fof(f1511,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,sK9(sK0,X1)))
        | ~ r1_lattice3(sK0,X1,X0)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_268 ),
    inference(subsumption_resolution,[],[f1510,f154])).

fof(f1510,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,sK9(sK0,X1)))
        | ~ r1_lattice3(sK0,X1,X0)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_268 ),
    inference(subsumption_resolution,[],[f1509,f168])).

fof(f1509,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,sK9(sK0,X1)))
        | ~ r1_lattice3(sK0,X1,X0)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_14
    | ~ spl15_268 ),
    inference(subsumption_resolution,[],[f1508,f193])).

fof(f1508,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,sK9(sK0,X1)))
        | ~ r1_lattice3(sK0,X1,X0)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ v25_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_268 ),
    inference(duplicate_literal_removal,[],[f1507])).

fof(f1507,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,sK9(sK0,X1)))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,sK9(sK0,X1)))
        | ~ r1_lattice3(sK0,X1,X0)
        | r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | ~ v25_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_268 ),
    inference(resolution,[],[f1502,f114])).

fof(f1502,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(sK9(sK0,X11),u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,X11,sK3(sK0,X11,sK9(sK0,X11)))
        | r1_orders_2(sK0,X12,sK2(sK0,X11,sK9(sK0,X11)))
        | ~ r1_lattice3(sK0,X11,X12)
        | r2_yellow_0(sK0,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X11) )
    | ~ spl15_268 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f1567,plain,
    ( spl15_280
    | ~ spl15_6
    | spl15_31
    | ~ spl15_252 ),
    inference(avatar_split_clause,[],[f1373,f1359,f256,f167,f1565])).

fof(f1373,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(sK0,sK1,X2),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1,X2),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_252 ),
    inference(subsumption_resolution,[],[f1372,f168])).

fof(f1372,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(sK0,sK1,X2),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1,X2),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_31
    | ~ spl15_252 ),
    inference(subsumption_resolution,[],[f1365,f257])).

fof(f1365,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3(sK0,sK1,X2),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,sK1,X2),sK9(sK0,sK1))
        | m1_subset_1(sK2(sK0,sK1,X2),u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK1)
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_252 ),
    inference(resolution,[],[f1360,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1552,plain,
    ( spl15_274
    | ~ spl15_6
    | spl15_31
    | ~ spl15_252 ),
    inference(avatar_split_clause,[],[f1369,f1359,f256,f167,f1550])).

fof(f1369,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl15_6
    | ~ spl15_31
    | ~ spl15_252 ),
    inference(subsumption_resolution,[],[f1368,f168])).

fof(f1368,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,sK1,X0),sK9(sK0,sK1))
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_31
    | ~ spl15_252 ),
    inference(subsumption_resolution,[],[f1363,f257])).

fof(f1363,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2(sK0,sK1,X0),sK9(sK0,sK1))
        | r2_yellow_0(sK0,sK1)
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_252 ),
    inference(resolution,[],[f1360,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1503,plain,
    ( spl15_268
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_90 ),
    inference(avatar_split_clause,[],[f1320,f553,f192,f167,f153,f146,f1501])).

fof(f553,plain,
    ( spl15_90
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,X0,sK2(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_90])])).

fof(f1320,plain,
    ( ! [X12,X11] :
        ( ~ r1_lattice3(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,X11,sK3(sK0,X11,sK9(sK0,X11)))
        | r1_orders_2(sK0,X12,sK2(sK0,X11,sK9(sK0,X11)))
        | ~ m1_subset_1(sK9(sK0,X11),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X11) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_90 ),
    inference(subsumption_resolution,[],[f1319,f147])).

fof(f1319,plain,
    ( ! [X12,X11] :
        ( ~ r1_lattice3(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,X11,sK3(sK0,X11,sK9(sK0,X11)))
        | r1_orders_2(sK0,X12,sK2(sK0,X11,sK9(sK0,X11)))
        | ~ m1_subset_1(sK9(sK0,X11),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X11)
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_90 ),
    inference(subsumption_resolution,[],[f1318,f154])).

fof(f1318,plain,
    ( ! [X12,X11] :
        ( ~ r1_lattice3(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,X11,sK3(sK0,X11,sK9(sK0,X11)))
        | r1_orders_2(sK0,X12,sK2(sK0,X11,sK9(sK0,X11)))
        | ~ m1_subset_1(sK9(sK0,X11),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X11)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_14
    | ~ spl15_90 ),
    inference(subsumption_resolution,[],[f1317,f168])).

fof(f1317,plain,
    ( ! [X12,X11] :
        ( ~ r1_lattice3(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,X11,sK3(sK0,X11,sK9(sK0,X11)))
        | r1_orders_2(sK0,X12,sK2(sK0,X11,sK9(sK0,X11)))
        | ~ m1_subset_1(sK9(sK0,X11),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X11)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_14
    | ~ spl15_90 ),
    inference(subsumption_resolution,[],[f579,f193])).

fof(f579,plain,
    ( ! [X12,X11] :
        ( ~ r1_lattice3(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattice3(sK0,X11,sK3(sK0,X11,sK9(sK0,X11)))
        | r1_orders_2(sK0,X12,sK2(sK0,X11,sK9(sK0,X11)))
        | ~ m1_subset_1(sK9(sK0,X11),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X11)
        | ~ v25_waybel_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_90 ),
    inference(resolution,[],[f554,f115])).

fof(f554,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,X1,X2)
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,X2))
        | r1_orders_2(sK0,X0,sK2(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1) )
    | ~ spl15_90 ),
    inference(avatar_component_clause,[],[f553])).

fof(f1361,plain,
    ( spl15_252
    | spl15_17
    | ~ spl15_32
    | ~ spl15_248 ),
    inference(avatar_split_clause,[],[f1344,f1330,f264,f201,f1359])).

fof(f1330,plain,
    ( spl15_248
  <=> ! [X1,X0] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | r1_orders_2(sK0,X1,sK9(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_248])])).

fof(f1344,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X3)
        | r1_orders_2(sK0,X3,sK9(sK0,sK1)) )
    | ~ spl15_17
    | ~ spl15_32
    | ~ spl15_248 ),
    inference(subsumption_resolution,[],[f1338,f202])).

fof(f1338,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X3)
        | v1_xboole_0(sK1)
        | r1_orders_2(sK0,X3,sK9(sK0,sK1)) )
    | ~ spl15_32
    | ~ spl15_248 ),
    inference(resolution,[],[f1331,f265])).

fof(f1331,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | v1_xboole_0(X0)
        | r1_orders_2(sK0,X1,sK9(sK0,X0)) )
    | ~ spl15_248 ),
    inference(avatar_component_clause,[],[f1330])).

fof(f1332,plain,
    ( spl15_248
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f1305,f192,f167,f153,f146,f1330])).

fof(f1305,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | r1_orders_2(sK0,X1,sK9(sK0,X0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f1304,f147])).

fof(f1304,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | r1_orders_2(sK0,X1,sK9(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f1303,f154])).

fof(f1303,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | r1_orders_2(sK0,X1,sK9(sK0,X0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_6
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f1302,f168])).

fof(f1302,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | r1_orders_2(sK0,X1,sK9(sK0,X0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl15_14 ),
    inference(resolution,[],[f193,f116])).

fof(f116,plain,(
    ! [X6,X4,X0] :
      ( ~ v25_waybel_0(X0)
      | ~ r1_lattice3(X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X4)
      | r1_orders_2(X0,X6,sK9(X0,X4))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1294,plain,
    ( spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | ~ spl15_72 ),
    inference(avatar_contradiction_clause,[],[f1293])).

fof(f1293,plain,
    ( $false
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f1292,f147])).

fof(f1292,plain,
    ( v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f1291,f154])).

fof(f1291,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f1290,f168])).

fof(f1290,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_72 ),
    inference(subsumption_resolution,[],[f1285,f196])).

fof(f196,plain,
    ( ~ v25_waybel_0(sK0)
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl15_15
  <=> ~ v25_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f1285,plain,
    ( v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_72 ),
    inference(resolution,[],[f482,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK7(X0))
      | v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f482,plain,
    ( v1_xboole_0(sK7(sK0))
    | ~ spl15_72 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl15_72
  <=> v1_xboole_0(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).

fof(f1275,plain,
    ( ~ spl15_219
    | ~ spl15_237
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | spl15_241 ),
    inference(avatar_split_clause,[],[f1272,f1227,f195,f167,f153,f146,f1215,f1123])).

fof(f1123,plain,
    ( spl15_219
  <=> ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_219])])).

fof(f1215,plain,
    ( spl15_237
  <=> ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_237])])).

fof(f1227,plain,
    ( spl15_241
  <=> ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_241])])).

fof(f1272,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_241 ),
    inference(subsumption_resolution,[],[f1271,f147])).

fof(f1271,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_241 ),
    inference(subsumption_resolution,[],[f1270,f154])).

fof(f1270,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_241 ),
    inference(subsumption_resolution,[],[f1269,f168])).

fof(f1269,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_241 ),
    inference(subsumption_resolution,[],[f1268,f196])).

fof(f1268,plain,
    ( v25_waybel_0(sK0)
    | ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_241 ),
    inference(resolution,[],[f1228,f119])).

fof(f119,plain,(
    ! [X2,X0] :
      ( m1_subset_1(sK8(X0,X2),u1_struct_0(X0))
      | v25_waybel_0(X0)
      | ~ r1_lattice3(X0,sK7(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1228,plain,
    ( ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ spl15_241 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1267,plain,
    ( ~ spl15_219
    | ~ spl15_237
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | spl15_239 ),
    inference(avatar_split_clause,[],[f1240,f1221,f195,f167,f153,f146,f1215,f1123])).

fof(f1221,plain,
    ( spl15_239
  <=> ~ r1_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_239])])).

fof(f1240,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_239 ),
    inference(subsumption_resolution,[],[f1239,f147])).

fof(f1239,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_239 ),
    inference(subsumption_resolution,[],[f1238,f154])).

fof(f1238,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_239 ),
    inference(subsumption_resolution,[],[f1237,f168])).

fof(f1237,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_239 ),
    inference(subsumption_resolution,[],[f1236,f196])).

fof(f1236,plain,
    ( v25_waybel_0(sK0)
    | ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_239 ),
    inference(resolution,[],[f1222,f120])).

fof(f120,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,sK7(X0),sK8(X0,X2))
      | v25_waybel_0(X0)
      | ~ r1_lattice3(X0,sK7(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1222,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ spl15_239 ),
    inference(avatar_component_clause,[],[f1221])).

fof(f1235,plain,
    ( ~ spl15_6
    | ~ spl15_74
    | spl15_237 ),
    inference(avatar_contradiction_clause,[],[f1234])).

fof(f1234,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_74
    | ~ spl15_237 ),
    inference(subsumption_resolution,[],[f1233,f168])).

fof(f1233,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_74
    | ~ spl15_237 ),
    inference(subsumption_resolution,[],[f1231,f488])).

fof(f488,plain,
    ( r2_yellow_0(sK0,sK7(sK0))
    | ~ spl15_74 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl15_74
  <=> r2_yellow_0(sK0,sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_74])])).

fof(f1231,plain,
    ( ~ r2_yellow_0(sK0,sK7(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_237 ),
    inference(resolution,[],[f1216,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1216,plain,
    ( ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ spl15_237 ),
    inference(avatar_component_clause,[],[f1215])).

fof(f1229,plain,
    ( ~ spl15_219
    | ~ spl15_237
    | ~ spl15_239
    | ~ spl15_241
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | ~ spl15_104 ),
    inference(avatar_split_clause,[],[f715,f672,f195,f167,f153,f146,f1227,f1221,f1215,f1123])).

fof(f672,plain,
    ( spl15_104
  <=> ! [X2] :
        ( ~ r1_lattice3(sK0,sK7(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK4(sK0,sK7(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_104])])).

fof(f715,plain,
    ( ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_104 ),
    inference(subsumption_resolution,[],[f714,f147])).

fof(f714,plain,
    ( ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_104 ),
    inference(subsumption_resolution,[],[f713,f154])).

fof(f713,plain,
    ( ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_104 ),
    inference(subsumption_resolution,[],[f712,f168])).

fof(f712,plain,
    ( ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_104 ),
    inference(subsumption_resolution,[],[f706,f196])).

fof(f706,plain,
    ( ~ m1_subset_1(sK8(sK0,sK4(sK0,sK7(sK0))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK7(sK0),sK8(sK0,sK4(sK0,sK7(sK0))))
    | v25_waybel_0(sK0)
    | ~ r1_lattice3(sK0,sK7(sK0),sK4(sK0,sK7(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_104 ),
    inference(resolution,[],[f673,f121])).

fof(f121,plain,(
    ! [X2,X0] :
      ( ~ r1_orders_2(X0,sK8(X0,X2),X2)
      | v25_waybel_0(X0)
      | ~ r1_lattice3(X0,sK7(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f673,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,X2,sK4(sK0,sK7(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK7(sK0),X2) )
    | ~ spl15_104 ),
    inference(avatar_component_clause,[],[f672])).

fof(f1134,plain,
    ( ~ spl15_6
    | ~ spl15_74
    | spl15_219 ),
    inference(avatar_contradiction_clause,[],[f1133])).

fof(f1133,plain,
    ( $false
    | ~ spl15_6
    | ~ spl15_74
    | ~ spl15_219 ),
    inference(subsumption_resolution,[],[f1132,f168])).

fof(f1132,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl15_74
    | ~ spl15_219 ),
    inference(subsumption_resolution,[],[f1130,f488])).

fof(f1130,plain,
    ( ~ r2_yellow_0(sK0,sK7(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl15_219 ),
    inference(resolution,[],[f1124,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1124,plain,
    ( ~ m1_subset_1(sK4(sK0,sK7(sK0)),u1_struct_0(sK0))
    | ~ spl15_219 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f674,plain,
    ( spl15_104
    | ~ spl15_6
    | ~ spl15_74 ),
    inference(avatar_split_clause,[],[f495,f487,f167,f672])).

fof(f495,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK0,sK7(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK4(sK0,sK7(sK0))) )
    | ~ spl15_6
    | ~ spl15_74 ),
    inference(subsumption_resolution,[],[f492,f168])).

fof(f492,plain,
    ( ! [X2] :
        ( ~ r1_lattice3(sK0,sK7(sK0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK4(sK0,sK7(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl15_74 ),
    inference(resolution,[],[f488,f95])).

fof(f95,plain,(
    ! [X0,X1,X9] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | r1_orders_2(X0,X9,sK4(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f555,plain,
    ( spl15_90
    | ~ spl15_6 ),
    inference(avatar_split_clause,[],[f447,f167,f553])).

fof(f447,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK2(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1) )
    | ~ spl15_6 ),
    inference(resolution,[],[f106,f168])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f489,plain,
    ( spl15_72
    | spl15_74
    | spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | spl15_15
    | ~ spl15_28 ),
    inference(avatar_split_clause,[],[f408,f248,f195,f167,f153,f146,f487,f481])).

fof(f248,plain,
    ( spl15_28
  <=> ! [X2] :
        ( r2_yellow_0(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f408,plain,
    ( r2_yellow_0(sK0,sK7(sK0))
    | v1_xboole_0(sK7(sK0))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_28 ),
    inference(subsumption_resolution,[],[f407,f147])).

fof(f407,plain,
    ( r2_yellow_0(sK0,sK7(sK0))
    | v1_xboole_0(sK7(sK0))
    | v2_struct_0(sK0)
    | ~ spl15_2
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_28 ),
    inference(subsumption_resolution,[],[f406,f154])).

fof(f406,plain,
    ( r2_yellow_0(sK0,sK7(sK0))
    | v1_xboole_0(sK7(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_6
    | ~ spl15_15
    | ~ spl15_28 ),
    inference(subsumption_resolution,[],[f405,f168])).

fof(f405,plain,
    ( r2_yellow_0(sK0,sK7(sK0))
    | v1_xboole_0(sK7(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_15
    | ~ spl15_28 ),
    inference(subsumption_resolution,[],[f402,f196])).

fof(f402,plain,
    ( r2_yellow_0(sK0,sK7(sK0))
    | v1_xboole_0(sK7(sK0))
    | v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl15_28 ),
    inference(resolution,[],[f249,f118])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f249,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_yellow_0(sK0,X2)
        | v1_xboole_0(X2) )
    | ~ spl15_28 ),
    inference(avatar_component_clause,[],[f248])).

fof(f266,plain,
    ( spl15_32
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f259,f192,f264])).

fof(f259,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f88,f193])).

fof(f88,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v25_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ( ~ r2_yellow_0(sK0,sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(sK1) )
      | ~ v25_waybel_0(sK0) )
    & ( ! [X2] :
          ( r2_yellow_0(sK0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
          | v1_xboole_0(X2) )
      | v25_waybel_0(sK0) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
          | ~ v25_waybel_0(X0) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X2) )
          | v25_waybel_0(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ~ r2_yellow_0(sK0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(sK0) )
      & ( ! [X2] :
            ( r2_yellow_0(sK0,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
            | v1_xboole_0(X2) )
        | v25_waybel_0(sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ~ r2_yellow_0(X0,sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X2] :
            ( r2_yellow_0(X0,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X2) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ( v25_waybel_0(X0)
      <~> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ( v25_waybel_0(X0)
      <~> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
        <=> ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X1) )
             => r2_yellow_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => r2_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t76_waybel_0.p',t76_waybel_0)).

fof(f258,plain,
    ( ~ spl15_31
    | ~ spl15_14 ),
    inference(avatar_split_clause,[],[f251,f192,f256])).

fof(f251,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ spl15_14 ),
    inference(subsumption_resolution,[],[f89,f193])).

fof(f89,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ v25_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f250,plain,
    ( spl15_28
    | spl15_15 ),
    inference(avatar_split_clause,[],[f242,f195,f248])).

fof(f242,plain,
    ( ! [X2] :
        ( r2_yellow_0(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2) )
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f86,f196])).

fof(f86,plain,(
    ! [X2] :
      ( r2_yellow_0(sK0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | v25_waybel_0(sK0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f203,plain,
    ( ~ spl15_15
    | ~ spl15_17 ),
    inference(avatar_split_clause,[],[f87,f201,f195])).

fof(f87,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f169,plain,(
    spl15_6 ),
    inference(avatar_split_clause,[],[f85,f167])).

fof(f85,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f162,plain,(
    spl15_4 ),
    inference(avatar_split_clause,[],[f84,f160])).

fof(f84,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f155,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f83,f153])).

fof(f83,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f148,plain,(
    ~ spl15_1 ),
    inference(avatar_split_clause,[],[f82,f146])).

fof(f82,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
