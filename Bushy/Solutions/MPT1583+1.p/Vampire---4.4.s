%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t62_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:46 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 618 expanded)
%              Number of leaves         :   34 ( 219 expanded)
%              Depth                    :   17
%              Number of atoms          :  922 (3022 expanded)
%              Number of equality atoms :   14 ( 114 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2370,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f93,f97,f111,f115,f129,f133,f139,f143,f180,f187,f222,f1437,f1439,f1456,f1472,f1543,f1611,f2289,f2298,f2307,f2345,f2359,f2363,f2365,f2367,f2369])).

fof(f2369,plain,
    ( spl11_26
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f82,f185,f178])).

fof(f178,plain,
    ( spl11_26
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f185,plain,
    ( spl11_31
  <=> ~ r2_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f82,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f48,f50])).

fof(f50,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) )
                    | ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) )
                    | ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X3 = X4
                   => ( ( r2_lattice3(X0,X2,X3)
                       => r2_lattice3(X1,X2,X4) )
                      & ( r1_lattice3(X0,X2,X3)
                       => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t62_yellow_0)).

fof(f48,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f2367,plain,
    ( spl11_26
    | ~ spl11_14
    | ~ spl11_18
    | spl11_41
    | spl11_215 ),
    inference(avatar_split_clause,[],[f2366,f2284,f227,f137,f127,f178])).

fof(f127,plain,
    ( spl11_14
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f137,plain,
    ( spl11_18
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f227,plain,
    ( spl11_41
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f2284,plain,
    ( spl11_215
  <=> ~ r2_hidden(sK5(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_215])])).

fof(f2366,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_41
    | ~ spl11_215 ),
    inference(subsumption_resolution,[],[f82,f2296])).

fof(f2296,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_41
    | ~ spl11_215 ),
    inference(resolution,[],[f2285,f1549])).

fof(f1549,plain,
    ( ! [X15] :
        ( r2_hidden(sK5(sK1,X15,sK3),u1_struct_0(sK1))
        | r2_lattice3(sK1,X15,sK3) )
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f322,f228])).

fof(f228,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f227])).

fof(f322,plain,
    ( ! [X15] :
        ( r2_lattice3(sK1,X15,sK3)
        | v1_xboole_0(u1_struct_0(sK1))
        | r2_hidden(sK5(sK1,X15,sK3),u1_struct_0(sK1)) )
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(resolution,[],[f168,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t2_subset)).

fof(f168,plain,
    ( ! [X6] :
        ( m1_subset_1(sK5(sK1,X6,sK3),u1_struct_0(sK1))
        | r2_lattice3(sK1,X6,sK3) )
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f161,f128])).

fof(f128,plain,
    ( l1_orders_2(sK1)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f161,plain,
    ( ! [X6] :
        ( ~ l1_orders_2(sK1)
        | m1_subset_1(sK5(sK1,X6,sK3),u1_struct_0(sK1))
        | r2_lattice3(sK1,X6,sK3) )
    | ~ spl11_18 ),
    inference(resolution,[],[f138,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
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
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',d9_lattice3)).

fof(f138,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f137])).

fof(f2285,plain,
    ( ~ r2_hidden(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl11_215 ),
    inference(avatar_component_clause,[],[f2284])).

fof(f2365,plain,
    ( spl11_26
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_212 ),
    inference(avatar_split_clause,[],[f2364,f2281,f137,f127,f178])).

fof(f2281,plain,
    ( spl11_212
  <=> r1_orders_2(sK1,sK5(sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_212])])).

fof(f2364,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_212 ),
    inference(subsumption_resolution,[],[f82,f2357])).

fof(f2357,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_212 ),
    inference(subsumption_resolution,[],[f2356,f128])).

fof(f2356,plain,
    ( ~ l1_orders_2(sK1)
    | r2_lattice3(sK1,sK2,sK3)
    | ~ spl11_18
    | ~ spl11_212 ),
    inference(subsumption_resolution,[],[f2355,f138])).

fof(f2355,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r2_lattice3(sK1,sK2,sK3)
    | ~ spl11_212 ),
    inference(resolution,[],[f2282,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2282,plain,
    ( r1_orders_2(sK1,sK5(sK1,sK2,sK3),sK3)
    | ~ spl11_212 ),
    inference(avatar_component_clause,[],[f2281])).

fof(f2363,plain,
    ( spl11_26
    | spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | spl11_217 ),
    inference(avatar_split_clause,[],[f2362,f2287,f137,f127,f113,f95,f91,f87,f178])).

fof(f87,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f91,plain,
    ( spl11_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f95,plain,
    ( spl11_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f113,plain,
    ( spl11_12
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f2287,plain,
    ( spl11_217
  <=> ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_217])])).

fof(f2362,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_217 ),
    inference(subsumption_resolution,[],[f82,f2305])).

fof(f2305,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_217 ),
    inference(resolution,[],[f2288,f315])).

fof(f315,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK1,X0,sK3),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,sK3) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(resolution,[],[f168,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f121,f92])).

fof(f92,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f121,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f120,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f120,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f117,f96])).

fof(f96,plain,
    ( l1_orders_2(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_12 ),
    inference(resolution,[],[f114,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t59_yellow_0)).

fof(f114,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f2288,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl11_217 ),
    inference(avatar_component_clause,[],[f2287])).

fof(f2359,plain,
    ( ~ spl11_14
    | ~ spl11_18
    | spl11_31
    | ~ spl11_212 ),
    inference(avatar_contradiction_clause,[],[f2358])).

fof(f2358,plain,
    ( $false
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_31
    | ~ spl11_212 ),
    inference(subsumption_resolution,[],[f2357,f186])).

fof(f186,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f185])).

fof(f2345,plain,
    ( ~ spl11_14
    | ~ spl11_18
    | spl11_29
    | ~ spl11_172 ),
    inference(avatar_contradiction_clause,[],[f2344])).

fof(f2344,plain,
    ( $false
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_29
    | ~ spl11_172 ),
    inference(subsumption_resolution,[],[f2343,f183])).

fof(f183,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl11_29
  <=> ~ r1_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f2343,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_172 ),
    inference(subsumption_resolution,[],[f2342,f128])).

fof(f2342,plain,
    ( ~ l1_orders_2(sK1)
    | r1_lattice3(sK1,sK2,sK3)
    | ~ spl11_18
    | ~ spl11_172 ),
    inference(subsumption_resolution,[],[f2341,f138])).

fof(f2341,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | r1_lattice3(sK1,sK2,sK3)
    | ~ spl11_172 ),
    inference(resolution,[],[f1452,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',d8_lattice3)).

fof(f1452,plain,
    ( r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3))
    | ~ spl11_172 ),
    inference(avatar_component_clause,[],[f1451])).

fof(f1451,plain,
    ( spl11_172
  <=> r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_172])])).

fof(f2307,plain,
    ( spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | spl11_31
    | spl11_217 ),
    inference(avatar_contradiction_clause,[],[f2306])).

fof(f2306,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_31
    | ~ spl11_217 ),
    inference(subsumption_resolution,[],[f2305,f186])).

fof(f2298,plain,
    ( ~ spl11_14
    | ~ spl11_18
    | spl11_31
    | spl11_41
    | spl11_215 ),
    inference(avatar_contradiction_clause,[],[f2297])).

fof(f2297,plain,
    ( $false
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_31
    | ~ spl11_41
    | ~ spl11_215 ),
    inference(subsumption_resolution,[],[f2296,f186])).

fof(f2289,plain,
    ( spl11_212
    | ~ spl11_215
    | ~ spl11_217
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_182 ),
    inference(avatar_split_clause,[],[f1633,f1609,f137,f131,f113,f109,f95,f2287,f2284,f2281])).

fof(f109,plain,
    ( spl11_10
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f131,plain,
    ( spl11_16
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f1609,plain,
    ( spl11_182
  <=> r1_orders_2(sK0,sK5(sK1,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_182])])).

fof(f1633,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_orders_2(sK1,sK5(sK1,sK2,sK3),sK3)
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_182 ),
    inference(subsumption_resolution,[],[f1632,f138])).

fof(f1632,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_orders_2(sK1,sK5(sK1,sK2,sK3),sK3)
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_182 ),
    inference(subsumption_resolution,[],[f1631,f132])).

fof(f132,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1631,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_orders_2(sK1,sK5(sK1,sK2,sK3),sK3)
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_182 ),
    inference(resolution,[],[f1610,f125])).

fof(f125,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,u1_struct_0(sK1))
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f124,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t1_subset)).

fof(f124,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r2_hidden(X1,u1_struct_0(sK1))
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f123,f96])).

fof(f123,plain,
    ( ! [X2,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r2_hidden(X1,u1_struct_0(sK1))
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl11_10
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f118,f110])).

fof(f110,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f118,plain,
    ( ! [X2,X1] :
        ( ~ v4_yellow_0(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r2_hidden(X1,u1_struct_0(sK1))
        | r1_orders_2(sK1,X1,X2) )
    | ~ spl11_12 ),
    inference(resolution,[],[f114,f80])).

fof(f80,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X3 != X5
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X2 != X4
      | X3 != X5
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',t61_yellow_0)).

fof(f1610,plain,
    ( r1_orders_2(sK0,sK5(sK1,sK2,sK3),sK3)
    | ~ spl11_182 ),
    inference(avatar_component_clause,[],[f1609])).

fof(f1611,plain,
    ( spl11_182
    | spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_24
    | spl11_31 ),
    inference(avatar_split_clause,[],[f1604,f185,f175,f137,f131,f127,f113,f95,f91,f87,f1609])).

fof(f175,plain,
    ( spl11_24
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f1604,plain,
    ( r1_orders_2(sK0,sK5(sK1,sK2,sK3),sK3)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_24
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f1603,f132])).

fof(f1603,plain,
    ( r1_orders_2(sK0,sK5(sK1,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_24
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f1602,f186])).

fof(f1602,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | r1_orders_2(sK0,sK5(sK1,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_24 ),
    inference(resolution,[],[f1460,f176])).

fof(f176,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1460,plain,
    ( ! [X4,X5] :
        ( ~ r2_lattice3(sK0,X5,X4)
        | r2_lattice3(sK1,X5,sK3)
        | r1_orders_2(sK0,sK5(sK1,X5,sK3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f1459])).

fof(f1459,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_lattice3(sK1,X5,sK3)
        | r1_orders_2(sK0,sK5(sK1,X5,sK3),X4)
        | ~ r2_lattice3(sK0,X5,X4)
        | r2_lattice3(sK1,X5,sK3) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(resolution,[],[f483,f169])).

fof(f169,plain,
    ( ! [X7] :
        ( r2_hidden(sK5(sK1,X7,sK3),X7)
        | r2_lattice3(sK1,X7,sK3) )
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f162,f128])).

fof(f162,plain,
    ( ! [X7] :
        ( ~ l1_orders_2(sK1)
        | r2_hidden(sK5(sK1,X7,sK3),X7)
        | r2_lattice3(sK1,X7,sK3) )
    | ~ spl11_18 ),
    inference(resolution,[],[f138,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f483,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(sK5(sK1,X7,sK3),X9)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r2_lattice3(sK1,X7,sK3)
        | r1_orders_2(sK0,sK5(sK1,X7,sK3),X8)
        | ~ r2_lattice3(sK0,X9,X8) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f476,f96])).

fof(f476,plain,
    ( ! [X8,X7,X9] :
        ( r2_lattice3(sK1,X7,sK3)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK5(sK1,X7,sK3),X9)
        | r1_orders_2(sK0,sK5(sK1,X7,sK3),X8)
        | ~ r2_lattice3(sK0,X9,X8) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(resolution,[],[f315,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1543,plain,
    ( spl11_1
    | ~ spl11_20
    | ~ spl11_40 ),
    inference(avatar_contradiction_clause,[],[f1542])).

fof(f1542,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_20
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f1541,f88])).

fof(f1541,plain,
    ( v2_struct_0(sK1)
    | ~ spl11_20
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f1521,f142])).

fof(f142,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl11_20
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f1521,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl11_40 ),
    inference(resolution,[],[f221,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',fc2_struct_0)).

fof(f221,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl11_40
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f1472,plain,
    ( spl11_28
    | ~ spl11_14
    | ~ spl11_18
    | spl11_175 ),
    inference(avatar_split_clause,[],[f1463,f1454,f137,f127,f1470])).

fof(f1470,plain,
    ( spl11_28
  <=> r1_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f1454,plain,
    ( spl11_175
  <=> ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_175])])).

fof(f1463,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_175 ),
    inference(resolution,[],[f1455,f165])).

fof(f165,plain,
    ( ! [X2] :
        ( m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK1))
        | r1_lattice3(sK1,X2,sK3) )
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f158,f128])).

fof(f158,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK1)
        | m1_subset_1(sK6(sK1,X2,sK3),u1_struct_0(sK1))
        | r1_lattice3(sK1,X2,sK3) )
    | ~ spl11_18 ),
    inference(resolution,[],[f138,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1455,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl11_175 ),
    inference(avatar_component_clause,[],[f1454])).

fof(f1456,plain,
    ( spl11_172
    | ~ spl11_175
    | spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_38
    | ~ spl11_170 ),
    inference(avatar_split_clause,[],[f1443,f1435,f217,f131,f113,f109,f95,f91,f87,f1454,f1451])).

fof(f217,plain,
    ( spl11_38
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f1435,plain,
    ( spl11_170
  <=> r1_orders_2(sK0,sK3,sK6(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_170])])).

fof(f1443,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_38
    | ~ spl11_170 ),
    inference(subsumption_resolution,[],[f1442,f122])).

fof(f1442,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3))
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_38
    | ~ spl11_170 ),
    inference(subsumption_resolution,[],[f1441,f218])).

fof(f218,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1441,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3))
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_16
    | ~ spl11_170 ),
    inference(subsumption_resolution,[],[f1440,f132])).

fof(f1440,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_hidden(sK3,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3))
    | ~ spl11_4
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_170 ),
    inference(resolution,[],[f1436,f125])).

fof(f1436,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK1,sK2,sK3))
    | ~ spl11_170 ),
    inference(avatar_component_clause,[],[f1435])).

fof(f1439,plain,
    ( spl11_24
    | ~ spl11_29 ),
    inference(avatar_split_clause,[],[f85,f182,f175])).

fof(f85,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f45,f50])).

fof(f45,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f1437,plain,
    ( spl11_170
    | spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_26
    | spl11_29 ),
    inference(avatar_split_clause,[],[f1427,f182,f178,f137,f131,f127,f113,f95,f91,f87,f1435])).

fof(f1427,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK1,sK2,sK3))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_26
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f1426,f132])).

fof(f1426,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_26
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f1425,f183])).

fof(f1425,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | r1_orders_2(sK0,sK3,sK6(sK1,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18
    | ~ spl11_26 ),
    inference(resolution,[],[f1422,f179])).

fof(f179,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f178])).

fof(f1422,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice3(sK0,X5,X4)
        | r1_lattice3(sK1,X5,sK3)
        | r1_orders_2(sK0,X4,sK6(sK1,X5,sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f1421])).

fof(f1421,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattice3(sK1,X5,sK3)
        | r1_orders_2(sK0,X4,sK6(sK1,X5,sK3))
        | ~ r1_lattice3(sK0,X5,X4)
        | r1_lattice3(sK1,X5,sK3) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(resolution,[],[f452,f166])).

fof(f166,plain,
    ( ! [X3] :
        ( r2_hidden(sK6(sK1,X3,sK3),X3)
        | r1_lattice3(sK1,X3,sK3) )
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f159,f128])).

fof(f159,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK1)
        | r2_hidden(sK6(sK1,X3,sK3),X3)
        | r1_lattice3(sK1,X3,sK3) )
    | ~ spl11_18 ),
    inference(resolution,[],[f138,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f452,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK6(sK1,X0,sK3),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK1,X0,sK3)
        | r1_orders_2(sK0,X1,sK6(sK1,X0,sK3))
        | ~ r1_lattice3(sK0,X2,X1) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f445,f96])).

fof(f445,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(sK6(sK1,X0,sK3),X2)
        | r1_orders_2(sK0,X1,sK6(sK1,X0,sK3))
        | ~ r1_lattice3(sK0,X2,X1) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(resolution,[],[f296,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f296,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK1,X0,sK3) )
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(resolution,[],[f165,f122])).

fof(f222,plain,
    ( spl11_38
    | spl11_40
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f163,f137,f220,f217])).

fof(f163,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl11_18 ),
    inference(resolution,[],[f138,f67])).

fof(f187,plain,
    ( ~ spl11_29
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f84,f185,f182])).

fof(f84,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) ),
    inference(forward_demodulation,[],[f83,f50])).

fof(f83,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(forward_demodulation,[],[f46,f50])).

fof(f46,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f180,plain,
    ( spl11_24
    | spl11_26 ),
    inference(avatar_split_clause,[],[f47,f178,f175])).

fof(f47,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f143,plain,
    ( spl11_20
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f134,f127,f141])).

fof(f134,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_14 ),
    inference(resolution,[],[f128,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',dt_l1_orders_2)).

fof(f139,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f81,f137])).

fof(f81,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f49,f50])).

fof(f49,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f51,f131])).

fof(f51,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f129,plain,
    ( spl11_14
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f119,f113,f95,f127])).

fof(f119,plain,
    ( l1_orders_2(sK1)
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f116,f96])).

fof(f116,plain,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK1)
    | ~ spl11_12 ),
    inference(resolution,[],[f114,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t62_yellow_0.p',dt_m1_yellow_0)).

fof(f115,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f54,f113])).

fof(f54,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f111,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f53,f109])).

fof(f53,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f56,f95])).

fof(f56,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f55,f91])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f52,f87])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
