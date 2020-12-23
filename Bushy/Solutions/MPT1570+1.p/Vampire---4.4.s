%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t48_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:43 EDT 2019

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  306 ( 961 expanded)
%              Number of leaves         :   56 ( 422 expanded)
%              Depth                    :   15
%              Number of atoms          : 1609 (7471 expanded)
%              Number of equality atoms :   46 ( 428 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f116,f123,f145,f167,f213,f270,f445,f474,f1199,f1204,f1284,f1289,f1341,f1347,f1348,f1368,f1372,f1373,f1377,f1388,f1412,f1423,f1542,f1564,f1690,f1704,f1737,f1796,f1826,f1868,f1907,f1916,f1971,f1977,f2032,f2033,f2054,f2134,f2152])).

fof(f2152,plain,
    ( ~ spl10_24
    | ~ spl10_70
    | spl10_73 ),
    inference(avatar_contradiction_clause,[],[f2151])).

fof(f2151,plain,
    ( $false
    | ~ spl10_24
    | ~ spl10_70
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f2150,f212])).

fof(f212,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl10_24
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f2150,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_70
    | ~ spl10_73 ),
    inference(subsumption_resolution,[],[f2148,f456])).

fof(f456,plain,
    ( r1_lattice3(sK0,sK1,sK5(sK0,sK1))
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl10_70
  <=> r1_lattice3(sK0,sK1,sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f2148,plain,
    ( ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_73 ),
    inference(resolution,[],[f462,f50])).

fof(f50,plain,(
    ! [X3] :
      ( r1_lattice3(sK0,sK2,X3)
      | ~ r1_lattice3(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    & r2_yellow_0(sK0,sK1)
    & ! [X3] :
        ( ( ( r1_lattice3(sK0,sK1,X3)
            | ~ r1_lattice3(sK0,sK2,X3) )
          & ( r1_lattice3(sK0,sK2,X3)
            | ~ r1_lattice3(sK0,sK1,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & ! [X3] :
                ( ( ( r1_lattice3(X0,X1,X3)
                    | ~ r1_lattice3(X0,X2,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                    | ~ r1_lattice3(X0,X1,X3) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ~ r2_yellow_0(sK0,X2)
          & r2_yellow_0(sK0,X1)
          & ! [X3] :
              ( ( ( r1_lattice3(sK0,X1,X3)
                  | ~ r1_lattice3(sK0,X2,X3) )
                & ( r1_lattice3(sK0,X2,X3)
                  | ~ r1_lattice3(sK0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X2,X3)
                  | ~ r1_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
     => ( ~ r2_yellow_0(X0,sK2)
        & r2_yellow_0(X0,sK1)
        & ! [X3] :
            ( ( ( r1_lattice3(X0,sK1,X3)
                | ~ r1_lattice3(X0,sK2,X3) )
              & ( r1_lattice3(X0,sK2,X3)
                | ~ r1_lattice3(X0,sK1,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X2,X3)
                  | ~ r1_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( r2_yellow_0(X0,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                  <=> r1_lattice3(X0,X2,X3) ) ) )
           => r2_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t48_yellow_0.p',t48_yellow_0)).

fof(f462,plain,
    ( ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl10_73
  <=> ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f2134,plain,
    ( spl10_260
    | spl10_11
    | ~ spl10_24
    | ~ spl10_70
    | spl10_153
    | ~ spl10_288 ),
    inference(avatar_split_clause,[],[f2129,f2022,f775,f455,f211,f121,f1794])).

fof(f1794,plain,
    ( spl10_260
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK3(sK0,sK2,sK5(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_260])])).

fof(f121,plain,
    ( spl10_11
  <=> ~ r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f775,plain,
    ( spl10_153
  <=> ~ r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_153])])).

fof(f2022,plain,
    ( spl10_288
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,X1,sK5(sK0,sK1))
        | r1_orders_2(sK0,X0,sK3(sK0,X1,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_288])])).

fof(f2129,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X2) )
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_70
    | ~ spl10_153
    | ~ spl10_288 ),
    inference(subsumption_resolution,[],[f2066,f776])).

fof(f776,plain,
    ( ~ r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_153 ),
    inference(avatar_component_clause,[],[f775])).

fof(f2066,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X2) )
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_70
    | ~ spl10_288 ),
    inference(subsumption_resolution,[],[f2065,f212])).

fof(f2065,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X2)
        | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) )
    | ~ spl10_11
    | ~ spl10_70
    | ~ spl10_288 ),
    inference(subsumption_resolution,[],[f2064,f456])).

fof(f2064,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X2)
        | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1))
        | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) )
    | ~ spl10_11
    | ~ spl10_288 ),
    inference(subsumption_resolution,[],[f2061,f122])).

fof(f122,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f2061,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,sK2)
        | ~ r1_lattice3(sK0,sK2,X2)
        | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1))
        | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) )
    | ~ spl10_288 ),
    inference(resolution,[],[f2023,f50])).

fof(f2023,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X1,sK5(sK0,sK1))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,sK5(sK0,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3(sK0,X1,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,X0) )
    | ~ spl10_288 ),
    inference(avatar_component_clause,[],[f2022])).

fof(f2054,plain,
    ( spl10_260
    | spl10_11
    | ~ spl10_24
    | ~ spl10_70
    | spl10_203
    | ~ spl10_286 ),
    inference(avatar_split_clause,[],[f2053,f2016,f1279,f455,f211,f121,f1794])).

fof(f1279,plain,
    ( spl10_203
  <=> ~ m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_203])])).

fof(f2016,plain,
    ( spl10_286
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X1,sK5(sK0,sK1)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,sK5(sK0,sK1))
        | r1_orders_2(sK0,X0,sK3(sK0,X1,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_286])])).

fof(f2053,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X2) )
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_70
    | ~ spl10_203
    | ~ spl10_286 ),
    inference(subsumption_resolution,[],[f2052,f212])).

fof(f2052,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X2)
        | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) )
    | ~ spl10_11
    | ~ spl10_70
    | ~ spl10_203
    | ~ spl10_286 ),
    inference(subsumption_resolution,[],[f2051,f456])).

fof(f2051,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X2)
        | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1))
        | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) )
    | ~ spl10_11
    | ~ spl10_203
    | ~ spl10_286 ),
    inference(subsumption_resolution,[],[f2050,f122])).

fof(f2050,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,sK2)
        | ~ r1_lattice3(sK0,sK2,X2)
        | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1))
        | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) )
    | ~ spl10_203
    | ~ spl10_286 ),
    inference(subsumption_resolution,[],[f2046,f1280])).

fof(f1280,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_203 ),
    inference(avatar_component_clause,[],[f1279])).

fof(f2046,plain,
    ( ! [X2] :
        ( m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,sK2,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,sK2)
        | ~ r1_lattice3(sK0,sK2,X2)
        | ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1))
        | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) )
    | ~ spl10_286 ),
    inference(resolution,[],[f2017,f50])).

fof(f2017,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X1,sK5(sK0,sK1))
        | m1_subset_1(sK4(sK0,X1,sK5(sK0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3(sK0,X1,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,X0) )
    | ~ spl10_286 ),
    inference(avatar_component_clause,[],[f2016])).

fof(f2033,plain,
    ( spl10_288
    | ~ spl10_8
    | ~ spl10_222 ),
    inference(avatar_split_clause,[],[f1705,f1375,f114,f2022])).

fof(f114,plain,
    ( spl10_8
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f1375,plain,
    ( spl10_222
  <=> ! [X5,X4,X6] :
        ( ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_lattice3(sK0,X4,sK4(sK0,X4,sK5(sK0,X6)))
        | ~ r1_lattice3(sK0,X4,sK5(sK0,X6))
        | r1_orders_2(sK0,X5,sK3(sK0,X4,sK5(sK0,X6)))
        | r2_yellow_0(sK0,X4)
        | ~ r2_yellow_0(sK0,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_222])])).

fof(f1705,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,X1,sK5(sK0,sK1))
        | r1_orders_2(sK0,X0,sK3(sK0,X1,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,X0) )
    | ~ spl10_8
    | ~ spl10_222 ),
    inference(resolution,[],[f1376,f115])).

fof(f115,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1376,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_yellow_0(sK0,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_lattice3(sK0,X4,sK4(sK0,X4,sK5(sK0,X6)))
        | ~ r1_lattice3(sK0,X4,sK5(sK0,X6))
        | r1_orders_2(sK0,X5,sK3(sK0,X4,sK5(sK0,X6)))
        | r2_yellow_0(sK0,X4)
        | ~ r1_lattice3(sK0,X4,X5) )
    | ~ spl10_222 ),
    inference(avatar_component_clause,[],[f1375])).

fof(f2032,plain,
    ( spl10_286
    | ~ spl10_8
    | ~ spl10_220 ),
    inference(avatar_split_clause,[],[f1703,f1370,f114,f2016])).

fof(f1370,plain,
    ( spl10_220
  <=> ! [X5,X4,X6] :
        ( ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X4,sK5(sK0,X6)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X4,sK5(sK0,X6))
        | r1_orders_2(sK0,X5,sK3(sK0,X4,sK5(sK0,X6)))
        | r2_yellow_0(sK0,X4)
        | ~ r2_yellow_0(sK0,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_220])])).

fof(f1703,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X1,sK5(sK0,sK1)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,sK5(sK0,sK1))
        | r1_orders_2(sK0,X0,sK3(sK0,X1,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X1,X0) )
    | ~ spl10_8
    | ~ spl10_220 ),
    inference(resolution,[],[f1371,f115])).

fof(f1371,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_yellow_0(sK0,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X4,sK5(sK0,X6)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X4,sK5(sK0,X6))
        | r1_orders_2(sK0,X5,sK3(sK0,X4,sK5(sK0,X6)))
        | r2_yellow_0(sK0,X4)
        | ~ r1_lattice3(sK0,X4,X5) )
    | ~ spl10_220 ),
    inference(avatar_component_clause,[],[f1370])).

fof(f1977,plain,
    ( ~ spl10_2
    | ~ spl10_8
    | ~ spl10_142
    | spl10_165
    | spl10_175
    | ~ spl10_218 ),
    inference(avatar_contradiction_clause,[],[f1974])).

fof(f1974,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_142
    | ~ spl10_165
    | ~ spl10_175
    | ~ spl10_218 ),
    inference(unit_resulting_resolution,[],[f94,f115,f1364,f745,f827,f991,f60])).

fof(f60,plain,(
    ! [X0,X7,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK6(X0,X1,X7))
      | ~ r1_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | sK5(X0,X1) = X7
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( sK3(X0,X1,X2) != X2
                  & ! [X4] :
                      ( r1_orders_2(X0,X4,sK3(X0,X1,X2))
                      | ~ r1_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X7] :
                  ( sK5(X0,X1) = X7
                  | ( ~ r1_orders_2(X0,sK6(X0,X1,X7),X7)
                    & r1_lattice3(X0,X1,sK6(X0,X1,X7))
                    & m1_subset_1(sK6(X0,X1,X7),u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X7)
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X9] :
                  ( r1_orders_2(X0,X9,sK5(X0,X1))
                  | ~ r1_lattice3(X0,X1,X9)
                  | ~ m1_subset_1(X9,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK5(X0,X1))
              & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f36,f40,f39,f38,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK3(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,X4,sK3(X0,X1,X2))
            | ~ r1_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X5,X2)
          & r1_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
            ( sK5(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X8,X7)
                & r1_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,X9,sK5(X0,X1))
            | ~ r1_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X8,X7)
          & r1_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X7),X7)
        & r1_lattice3(X0,X1,sK6(X0,X1,X7))
        & m1_subset_1(sK6(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t48_yellow_0.p',d8_yellow_0)).

fof(f991,plain,
    ( ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))))
    | ~ spl10_175 ),
    inference(avatar_component_clause,[],[f990])).

fof(f990,plain,
    ( spl10_175
  <=> ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_175])])).

fof(f827,plain,
    ( sK3(sK0,sK2,sK5(sK0,sK1)) != sK5(sK0,sK1)
    | ~ spl10_165 ),
    inference(avatar_component_clause,[],[f826])).

fof(f826,plain,
    ( spl10_165
  <=> sK3(sK0,sK2,sK5(sK0,sK1)) != sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_165])])).

fof(f745,plain,
    ( r1_lattice3(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_142 ),
    inference(avatar_component_clause,[],[f744])).

fof(f744,plain,
    ( spl10_142
  <=> r1_lattice3(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_142])])).

fof(f1364,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_218 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f1363,plain,
    ( spl10_218
  <=> m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_218])])).

fof(f94,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl10_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1971,plain,
    ( ~ spl10_263
    | ~ spl10_174
    | spl10_177 ),
    inference(avatar_split_clause,[],[f1969,f993,f987,f1824])).

fof(f1824,plain,
    ( spl10_263
  <=> ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_263])])).

fof(f987,plain,
    ( spl10_174
  <=> r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_174])])).

fof(f993,plain,
    ( spl10_177
  <=> ~ r1_lattice3(sK0,sK2,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_177])])).

fof(f1969,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl10_174
    | ~ spl10_177 ),
    inference(subsumption_resolution,[],[f1968,f988])).

fof(f988,plain,
    ( r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))))
    | ~ spl10_174 ),
    inference(avatar_component_clause,[],[f987])).

fof(f1968,plain,
    ( ~ r1_lattice3(sK0,sK1,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl10_177 ),
    inference(resolution,[],[f994,f50])).

fof(f994,plain,
    ( ~ r1_lattice3(sK0,sK2,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))))
    | ~ spl10_177 ),
    inference(avatar_component_clause,[],[f993])).

fof(f1916,plain,
    ( ~ spl10_2
    | ~ spl10_8
    | ~ spl10_130
    | ~ spl10_202
    | spl10_269 ),
    inference(avatar_contradiction_clause,[],[f1915])).

fof(f1915,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_269 ),
    inference(subsumption_resolution,[],[f1914,f94])).

fof(f1914,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_8
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_269 ),
    inference(subsumption_resolution,[],[f1913,f115])).

fof(f1913,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_269 ),
    inference(subsumption_resolution,[],[f1912,f1283])).

fof(f1283,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_202 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f1282,plain,
    ( spl10_202
  <=> m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_202])])).

fof(f1912,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_130
    | ~ spl10_269 ),
    inference(subsumption_resolution,[],[f1910,f676])).

fof(f676,plain,
    ( r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_130 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl10_130
  <=> r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f1910,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_269 ),
    inference(resolution,[],[f1906,f58])).

fof(f58,plain,(
    ! [X0,X1,X9] :
      ( r1_orders_2(X0,X9,sK5(X0,X1))
      | ~ r1_lattice3(X0,X1,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1906,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK2,sK5(sK0,sK1)),sK5(sK0,sK1))
    | ~ spl10_269 ),
    inference(avatar_component_clause,[],[f1905])).

fof(f1905,plain,
    ( spl10_269
  <=> ~ r1_orders_2(sK0,sK4(sK0,sK2,sK5(sK0,sK1)),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_269])])).

fof(f1907,plain,
    ( ~ spl10_269
    | ~ spl10_2
    | spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(avatar_split_clause,[],[f1900,f829,f464,f211,f121,f93,f1905])).

fof(f464,plain,
    ( spl10_72
  <=> r1_lattice3(sK0,sK2,sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f829,plain,
    ( spl10_164
  <=> sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_164])])).

fof(f1900,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK2,sK5(sK0,sK1)),sK5(sK0,sK1))
    | ~ spl10_2
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1899,f94])).

fof(f1899,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK2,sK5(sK0,sK1)),sK5(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1898,f212])).

fof(f1898,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK2,sK5(sK0,sK1)),sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1897,f465])).

fof(f465,plain,
    ( r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f464])).

fof(f1897,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK2,sK5(sK0,sK1)),sK5(sK0,sK1))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1896,f122])).

fof(f1896,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ r1_orders_2(sK0,sK4(sK0,sK2,sK5(sK0,sK1)),sK5(sK0,sK1))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_164 ),
    inference(trivial_inequality_removal,[],[f1891])).

fof(f1891,plain,
    ( sK5(sK0,sK1) != sK5(sK0,sK1)
    | r2_yellow_0(sK0,sK2)
    | ~ r1_orders_2(sK0,sK4(sK0,sK2,sK5(sK0,sK1)),sK5(sK0,sK1))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_164 ),
    inference(superposition,[],[f73,f830])).

fof(f830,plain,
    ( sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ spl10_164 ),
    inference(avatar_component_clause,[],[f829])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1868,plain,
    ( spl10_164
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_142
    | ~ spl10_218
    | spl10_263 ),
    inference(avatar_split_clause,[],[f1849,f1824,f1363,f744,f114,f93,f829])).

fof(f1849,plain,
    ( sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_142
    | ~ spl10_218
    | ~ spl10_263 ),
    inference(subsumption_resolution,[],[f1848,f94])).

fof(f1848,plain,
    ( sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_8
    | ~ spl10_142
    | ~ spl10_218
    | ~ spl10_263 ),
    inference(subsumption_resolution,[],[f1847,f115])).

fof(f1847,plain,
    ( sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_142
    | ~ spl10_218
    | ~ spl10_263 ),
    inference(subsumption_resolution,[],[f1846,f1364])).

fof(f1846,plain,
    ( sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_142
    | ~ spl10_263 ),
    inference(subsumption_resolution,[],[f1838,f745])).

fof(f1838,plain,
    ( sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_263 ),
    inference(resolution,[],[f1825,f59])).

fof(f59,plain,(
    ! [X0,X7,X1] :
      ( m1_subset_1(sK6(X0,X1,X7),u1_struct_0(X0))
      | sK5(X0,X1) = X7
      | ~ r1_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1825,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl10_263 ),
    inference(avatar_component_clause,[],[f1824])).

fof(f1826,plain,
    ( ~ spl10_263
    | ~ spl10_36
    | ~ spl10_142
    | spl10_165
    | ~ spl10_176
    | ~ spl10_218
    | ~ spl10_260 ),
    inference(avatar_split_clause,[],[f1805,f1794,f1363,f996,f826,f744,f268,f1824])).

fof(f268,plain,
    ( spl10_36
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,X0),X0)
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f996,plain,
    ( spl10_176
  <=> r1_lattice3(sK0,sK2,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_176])])).

fof(f1805,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl10_36
    | ~ spl10_142
    | ~ spl10_165
    | ~ spl10_176
    | ~ spl10_218
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f1804,f827])).

fof(f1804,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0))
    | sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ spl10_36
    | ~ spl10_142
    | ~ spl10_176
    | ~ spl10_218
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f1803,f1364])).

fof(f1803,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ spl10_36
    | ~ spl10_142
    | ~ spl10_176
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f1802,f745])).

fof(f1802,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ spl10_36
    | ~ spl10_176
    | ~ spl10_260 ),
    inference(subsumption_resolution,[],[f1798,f997])).

fof(f997,plain,
    ( r1_lattice3(sK0,sK2,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))))
    | ~ spl10_176 ),
    inference(avatar_component_clause,[],[f996])).

fof(f1798,plain,
    ( ~ r1_lattice3(sK0,sK2,sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | sK3(sK0,sK2,sK5(sK0,sK1)) = sK5(sK0,sK1)
    | ~ spl10_36
    | ~ spl10_260 ),
    inference(resolution,[],[f1795,f269])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,X0),X0)
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK1) = X0 )
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f268])).

fof(f1795,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_260 ),
    inference(avatar_component_clause,[],[f1794])).

fof(f1796,plain,
    ( spl10_260
    | spl10_11
    | ~ spl10_72
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_248 ),
    inference(avatar_split_clause,[],[f1743,f1735,f1282,f675,f464,f121,f1794])).

fof(f1735,plain,
    ( spl10_248
  <=> ! [X1,X0] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,sK3(sK0,X0,sK5(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_248])])).

fof(f1743,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK3(sK0,sK2,sK5(sK0,sK1))) )
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_248 ),
    inference(subsumption_resolution,[],[f1742,f676])).

fof(f1742,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK3(sK0,sK2,sK5(sK0,sK1))) )
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_202
    | ~ spl10_248 ),
    inference(subsumption_resolution,[],[f1741,f465])).

fof(f1741,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK3(sK0,sK2,sK5(sK0,sK1))) )
    | ~ spl10_11
    | ~ spl10_202
    | ~ spl10_248 ),
    inference(subsumption_resolution,[],[f1738,f122])).

fof(f1738,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_yellow_0(sK0,sK2)
        | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK3(sK0,sK2,sK5(sK0,sK1))) )
    | ~ spl10_202
    | ~ spl10_248 ),
    inference(resolution,[],[f1736,f1283])).

fof(f1736,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,sK3(sK0,X0,sK5(sK0,sK1))) )
    | ~ spl10_248 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f1737,plain,
    ( spl10_248
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f529,f114,f93,f1735])).

fof(f529,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,sK3(sK0,X0,sK5(sK0,sK1))) )
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f528,f94])).

fof(f528,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ l1_orders_2(sK0)
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,sK3(sK0,X0,sK5(sK0,sK1))) )
    | ~ spl10_8 ),
    inference(resolution,[],[f273,f115])).

fof(f273,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_yellow_0(X0,X3)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK5(X0,X3))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X3,sK4(X0,X2,sK5(X0,X3)))
      | ~ m1_subset_1(sK4(X0,X2,sK5(X0,X3)),u1_struct_0(X0))
      | r1_orders_2(X0,X1,sK3(X0,X2,sK5(X0,X3))) ) ),
    inference(subsumption_resolution,[],[f272,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f272,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK3(X0,X2,sK5(X0,X3)))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK5(X0,X3))
      | ~ m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X3,sK4(X0,X2,sK5(X0,X3)))
      | ~ m1_subset_1(sK4(X0,X2,sK5(X0,X3)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X3) ) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK3(X0,X2,sK5(X0,X3)))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,sK5(X0,X3))
      | ~ m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X3,sK4(X0,X2,sK5(X0,X3)))
      | ~ m1_subset_1(sK4(X0,X2,sK5(X0,X3)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X3)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f70,f58])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r1_orders_2(X0,X4,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1704,plain,
    ( spl10_154
    | spl10_11
    | ~ spl10_72
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_216 ),
    inference(avatar_split_clause,[],[f1696,f1345,f1282,f675,f464,f121,f798])).

fof(f798,plain,
    ( spl10_154
  <=> r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f1345,plain,
    ( spl10_216
  <=> ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3(sK0,X0,sK5(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_216])])).

fof(f1696,plain,
    ( r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_216 ),
    inference(subsumption_resolution,[],[f1695,f122])).

fof(f1695,plain,
    ( r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_72
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_216 ),
    inference(subsumption_resolution,[],[f1694,f676])).

fof(f1694,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
    | r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_72
    | ~ spl10_202
    | ~ spl10_216 ),
    inference(subsumption_resolution,[],[f1691,f465])).

fof(f1691,plain,
    ( ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
    | r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_202
    | ~ spl10_216 ),
    inference(resolution,[],[f1346,f1283])).

fof(f1346,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK3(sK0,X0,sK5(sK0,sK1))) )
    | ~ spl10_216 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1690,plain,
    ( spl10_218
    | spl10_11
    | ~ spl10_72
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_214 ),
    inference(avatar_split_clause,[],[f1687,f1339,f1282,f675,f464,f121,f1363])).

fof(f1339,plain,
    ( spl10_214
  <=> ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_214])])).

fof(f1687,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_214 ),
    inference(subsumption_resolution,[],[f1686,f122])).

fof(f1686,plain,
    ( r2_yellow_0(sK0,sK2)
    | m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_72
    | ~ spl10_130
    | ~ spl10_202
    | ~ spl10_214 ),
    inference(subsumption_resolution,[],[f1685,f676])).

fof(f1685,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
    | r2_yellow_0(sK0,sK2)
    | m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_72
    | ~ spl10_202
    | ~ spl10_214 ),
    inference(subsumption_resolution,[],[f1682,f465])).

fof(f1682,plain,
    ( ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
    | r2_yellow_0(sK0,sK2)
    | m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_202
    | ~ spl10_214 ),
    inference(resolution,[],[f1340,f1283])).

fof(f1340,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | r2_yellow_0(sK0,X0)
        | m1_subset_1(sK3(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0)) )
    | ~ spl10_214 ),
    inference(avatar_component_clause,[],[f1339])).

fof(f1564,plain,
    ( ~ spl10_61
    | ~ spl10_18
    | spl10_25 ),
    inference(avatar_split_clause,[],[f1531,f208,f165,f407])).

fof(f407,plain,
    ( spl10_61
  <=> ~ m1_subset_1(sK5(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f165,plain,
    ( spl10_18
  <=> u1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f208,plain,
    ( spl10_25
  <=> ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f1531,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),k1_xboole_0)
    | ~ spl10_18
    | ~ spl10_25 ),
    inference(forward_demodulation,[],[f209,f166])).

fof(f166,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f209,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f208])).

fof(f1542,plain,
    ( ~ spl10_8
    | spl10_61
    | ~ spl10_66 ),
    inference(avatar_contradiction_clause,[],[f1541])).

fof(f1541,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_61
    | ~ spl10_66 ),
    inference(subsumption_resolution,[],[f1539,f408])).

fof(f408,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),k1_xboole_0)
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f407])).

fof(f1539,plain,
    ( m1_subset_1(sK5(sK0,sK1),k1_xboole_0)
    | ~ spl10_8
    | ~ spl10_66 ),
    inference(resolution,[],[f444,f115])).

fof(f444,plain,
    ( ! [X4] :
        ( ~ r2_yellow_0(sK0,X4)
        | m1_subset_1(sK5(sK0,X4),k1_xboole_0) )
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl10_66
  <=> ! [X4] :
        ( m1_subset_1(sK5(sK0,X4),k1_xboole_0)
        | ~ r2_yellow_0(sK0,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f1423,plain,
    ( spl10_218
    | ~ spl10_2
    | spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | spl10_153 ),
    inference(avatar_split_clause,[],[f1400,f775,f464,f211,f121,f93,f1363])).

fof(f1400,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_153 ),
    inference(subsumption_resolution,[],[f1399,f94])).

fof(f1399,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_153 ),
    inference(subsumption_resolution,[],[f1398,f212])).

fof(f1398,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_153 ),
    inference(subsumption_resolution,[],[f1397,f465])).

fof(f1397,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_153 ),
    inference(subsumption_resolution,[],[f1392,f122])).

fof(f1392,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_153 ),
    inference(resolution,[],[f776,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1412,plain,
    ( spl10_154
    | ~ spl10_2
    | spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | spl10_153 ),
    inference(avatar_split_clause,[],[f1396,f775,f464,f211,f121,f93,f798])).

fof(f1396,plain,
    ( r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_2
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_153 ),
    inference(subsumption_resolution,[],[f1395,f94])).

fof(f1395,plain,
    ( r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_153 ),
    inference(subsumption_resolution,[],[f1394,f212])).

fof(f1394,plain,
    ( r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_153 ),
    inference(subsumption_resolution,[],[f1393,f465])).

fof(f1393,plain,
    ( r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_153 ),
    inference(subsumption_resolution,[],[f1391,f122])).

fof(f1391,plain,
    ( r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_153 ),
    inference(resolution,[],[f776,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1388,plain,
    ( ~ spl10_2
    | spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | spl10_155
    | spl10_203 ),
    inference(avatar_contradiction_clause,[],[f1387])).

fof(f1387,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_155
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f1386,f94])).

fof(f1386,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_155
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f1385,f212])).

fof(f1385,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_155
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f1384,f465])).

fof(f1384,plain,
    ( ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_155
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f1383,f1280])).

fof(f1383,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_155 ),
    inference(subsumption_resolution,[],[f1381,f122])).

fof(f1381,plain,
    ( r2_yellow_0(sK0,sK2)
    | m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_155 ),
    inference(resolution,[],[f796,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f796,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_155 ),
    inference(avatar_component_clause,[],[f795])).

fof(f795,plain,
    ( spl10_155
  <=> ~ r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_155])])).

fof(f1377,plain,
    ( spl10_222
    | ~ spl10_2
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1226,f1202,f93,f1375])).

fof(f1202,plain,
    ( spl10_194
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_194])])).

fof(f1226,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_lattice3(sK0,X4,sK4(sK0,X4,sK5(sK0,X6)))
        | ~ r1_lattice3(sK0,X4,sK5(sK0,X6))
        | r1_orders_2(sK0,X5,sK3(sK0,X4,sK5(sK0,X6)))
        | r2_yellow_0(sK0,X4)
        | ~ r2_yellow_0(sK0,X6) )
    | ~ spl10_2
    | ~ spl10_194 ),
    inference(subsumption_resolution,[],[f1221,f94])).

fof(f1221,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r1_lattice3(sK0,X4,sK4(sK0,X4,sK5(sK0,X6)))
        | ~ r1_lattice3(sK0,X4,sK5(sK0,X6))
        | r1_orders_2(sK0,X5,sK3(sK0,X4,sK5(sK0,X6)))
        | r2_yellow_0(sK0,X4)
        | ~ r2_yellow_0(sK0,X6)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_194 ),
    inference(resolution,[],[f1203,f56])).

fof(f1203,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | r2_yellow_0(sK0,X1) )
    | ~ spl10_194 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1373,plain,
    ( spl10_218
    | ~ spl10_2
    | spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | spl10_203 ),
    inference(avatar_split_clause,[],[f1357,f1279,f464,f211,f121,f93,f1363])).

fof(f1357,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f1356,f94])).

fof(f1356,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f1355,f212])).

fof(f1355,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f1354,f465])).

fof(f1354,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f1353,f122])).

fof(f1353,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_203 ),
    inference(resolution,[],[f1280,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1372,plain,
    ( spl10_220
    | ~ spl10_2
    | ~ spl10_192 ),
    inference(avatar_split_clause,[],[f1211,f1197,f93,f1370])).

fof(f1197,plain,
    ( spl10_192
  <=> ! [X1,X0,X2] :
        ( r1_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_192])])).

fof(f1211,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X4,sK5(sK0,X6)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X4,sK5(sK0,X6))
        | r1_orders_2(sK0,X5,sK3(sK0,X4,sK5(sK0,X6)))
        | r2_yellow_0(sK0,X4)
        | ~ r2_yellow_0(sK0,X6) )
    | ~ spl10_2
    | ~ spl10_192 ),
    inference(subsumption_resolution,[],[f1206,f94])).

fof(f1206,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X4,sK5(sK0,X6)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X4,sK5(sK0,X6))
        | r1_orders_2(sK0,X5,sK3(sK0,X4,sK5(sK0,X6)))
        | r2_yellow_0(sK0,X4)
        | ~ r2_yellow_0(sK0,X6)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_192 ),
    inference(resolution,[],[f1198,f56])).

fof(f1198,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | r2_yellow_0(sK0,X1) )
    | ~ spl10_192 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f1368,plain,
    ( ~ spl10_219
    | spl10_143
    | ~ spl10_154 ),
    inference(avatar_split_clause,[],[f1343,f798,f741,f1366])).

fof(f1366,plain,
    ( spl10_219
  <=> ~ m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_219])])).

fof(f741,plain,
    ( spl10_143
  <=> ~ r1_lattice3(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_143])])).

fof(f1343,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_143
    | ~ spl10_154 ),
    inference(subsumption_resolution,[],[f1342,f742])).

fof(f742,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_143 ),
    inference(avatar_component_clause,[],[f741])).

fof(f1342,plain,
    ( r1_lattice3(sK0,sK1,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK3(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_154 ),
    inference(resolution,[],[f799,f51])).

fof(f51,plain,(
    ! [X3] :
      ( ~ r1_lattice3(sK0,sK2,X3)
      | r1_lattice3(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f799,plain,
    ( r1_lattice3(sK0,sK2,sK3(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_154 ),
    inference(avatar_component_clause,[],[f798])).

fof(f1348,plain,
    ( ~ spl10_203
    | spl10_131
    | ~ spl10_152 ),
    inference(avatar_split_clause,[],[f1292,f772,f678,f1279])).

fof(f678,plain,
    ( spl10_131
  <=> ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_131])])).

fof(f772,plain,
    ( spl10_152
  <=> r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_152])])).

fof(f1292,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_131
    | ~ spl10_152 ),
    inference(subsumption_resolution,[],[f1291,f679])).

fof(f679,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_131 ),
    inference(avatar_component_clause,[],[f678])).

fof(f1291,plain,
    ( r1_lattice3(sK0,sK1,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_152 ),
    inference(resolution,[],[f773,f51])).

fof(f773,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_152 ),
    inference(avatar_component_clause,[],[f772])).

fof(f1347,plain,
    ( spl10_216
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f526,f114,f93,f1345])).

fof(f526,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3(sK0,X0,sK5(sK0,sK1))) )
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f525,f94])).

fof(f525,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ l1_orders_2(sK0)
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3(sK0,X0,sK5(sK0,sK1))) )
    | ~ spl10_8 ),
    inference(resolution,[],[f258,f115])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK5(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,sK4(X0,X1,sK5(X0,X2)))
      | ~ m1_subset_1(sK4(X0,X1,sK5(X0,X2)),u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK3(X0,X1,sK5(X0,X2))) ) ),
    inference(subsumption_resolution,[],[f257,f56])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,sK5(X0,X2)))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK5(X0,X2))
      | ~ m1_subset_1(sK5(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,sK4(X0,X1,sK5(X0,X2)))
      | ~ m1_subset_1(sK4(X0,X1,sK5(X0,X2)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,sK5(X0,X2)))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK5(X0,X2))
      | ~ m1_subset_1(sK5(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,sK4(X0,X1,sK5(X0,X2)))
      | ~ m1_subset_1(sK4(X0,X1,sK5(X0,X2)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f67,f58])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1341,plain,
    ( spl10_214
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f520,f114,f93,f1339])).

fof(f520,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0)) )
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f519,f94])).

fof(f519,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK5(sK0,sK1))
        | ~ l1_orders_2(sK0)
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK5(sK0,sK1)))
        | ~ m1_subset_1(sK4(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0,X0,sK5(sK0,sK1)),u1_struct_0(sK0)) )
    | ~ spl10_8 ),
    inference(resolution,[],[f228,f115])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK5(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,sK4(X0,X1,sK5(X0,X2)))
      | ~ m1_subset_1(sK4(X0,X1,sK5(X0,X2)),u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,sK5(X0,X2)),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f227,f56])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,sK5(X0,X2)),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK5(X0,X2))
      | ~ m1_subset_1(sK5(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,sK4(X0,X1,sK5(X0,X2)))
      | ~ m1_subset_1(sK4(X0,X1,sK5(X0,X2)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,sK5(X0,X2)),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,sK5(X0,X2))
      | ~ m1_subset_1(sK5(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,sK4(X0,X1,sK5(X0,X2)))
      | ~ m1_subset_1(sK4(X0,X1,sK5(X0,X2)),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f64,f58])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1289,plain,
    ( spl10_152
    | ~ spl10_2
    | spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(avatar_split_clause,[],[f1268,f829,f464,f211,f121,f93,f772])).

fof(f1268,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ spl10_2
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1267,f94])).

fof(f1267,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1266,f212])).

fof(f1266,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1256,f465])).

fof(f1256,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1249,f122])).

fof(f1249,plain,
    ( r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_164 ),
    inference(trivial_inequality_removal,[],[f1246])).

fof(f1246,plain,
    ( sK5(sK0,sK1) != sK5(sK0,sK1)
    | r2_yellow_0(sK0,sK2)
    | r1_lattice3(sK0,sK2,sK4(sK0,sK2,sK5(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_164 ),
    inference(superposition,[],[f72,f830])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1284,plain,
    ( spl10_202
    | ~ spl10_2
    | spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(avatar_split_clause,[],[f1265,f829,f464,f211,f121,f93,f1282])).

fof(f1265,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1264,f94])).

fof(f1264,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_24
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1263,f212])).

fof(f1263,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_72
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1262,f465])).

fof(f1262,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_11
    | ~ spl10_164 ),
    inference(subsumption_resolution,[],[f1248,f122])).

fof(f1248,plain,
    ( r2_yellow_0(sK0,sK2)
    | m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_164 ),
    inference(trivial_inequality_removal,[],[f1247])).

fof(f1247,plain,
    ( sK5(sK0,sK1) != sK5(sK0,sK1)
    | r2_yellow_0(sK0,sK2)
    | m1_subset_1(sK4(sK0,sK2,sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK5(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_164 ),
    inference(superposition,[],[f71,f830])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1204,plain,
    ( spl10_194
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f265,f93,f1202])).

fof(f265,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1) )
    | ~ spl10_2 ),
    inference(resolution,[],[f69,f94])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,X4,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1199,plain,
    ( spl10_192
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f259,f93,f1197])).

fof(f259,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK3(sK0,X1,X2))
        | ~ r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_yellow_0(sK0,X1) )
    | ~ spl10_2 ),
    inference(resolution,[],[f68,f94])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,X4,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f474,plain,
    ( ~ spl10_2
    | ~ spl10_8
    | spl10_71 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_71 ),
    inference(subsumption_resolution,[],[f472,f94])).

fof(f472,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_8
    | ~ spl10_71 ),
    inference(subsumption_resolution,[],[f470,f115])).

fof(f470,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl10_71 ),
    inference(resolution,[],[f459,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f459,plain,
    ( ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1))
    | ~ spl10_71 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl10_71
  <=> ~ r1_lattice3(sK0,sK1,sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f445,plain,
    ( spl10_66
    | ~ spl10_2
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f388,f165,f93,f443])).

fof(f388,plain,
    ( ! [X4] :
        ( m1_subset_1(sK5(sK0,X4),k1_xboole_0)
        | ~ r2_yellow_0(sK0,X4) )
    | ~ spl10_2
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f376,f94])).

fof(f376,plain,
    ( ! [X4] :
        ( m1_subset_1(sK5(sK0,X4),k1_xboole_0)
        | ~ r2_yellow_0(sK0,X4)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_18 ),
    inference(superposition,[],[f56,f166])).

fof(f270,plain,
    ( spl10_36
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f157,f114,f93,f268])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,X0),X0)
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK1) = X0 )
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f156,f94])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,X0),X0)
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK1) = X0
        | ~ l1_orders_2(sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f61,f115])).

fof(f61,plain,(
    ! [X0,X7,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,sK6(X0,X1,X7),X7)
      | ~ r1_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | sK5(X0,X1) = X7
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f213,plain,
    ( spl10_24
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f205,f137,f211])).

fof(f137,plain,
    ( spl10_12
  <=> r2_hidden(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f205,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_12 ),
    inference(resolution,[],[f138,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t48_yellow_0.p',t1_subset)).

fof(f138,plain,
    ( r2_hidden(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f167,plain,
    ( spl10_18
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f149,f143,f165])).

fof(f143,plain,
    ( spl10_14
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f149,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl10_14 ),
    inference(resolution,[],[f144,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t48_yellow_0.p',t6_boole)).

fof(f144,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl10_12
    | spl10_14
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f132,f114,f93,f143,f137])).

fof(f132,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f131,f94])).

fof(f131,plain,
    ( ~ l1_orders_2(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(resolution,[],[f127,f115])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t48_yellow_0.p',t2_subset)).

fof(f123,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f53,f121])).

fof(f53,plain,(
    ~ r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f52,f114])).

fof(f52,plain,(
    r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
