%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t29_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:19 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 192 expanded)
%              Number of leaves         :   19 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  375 ( 818 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f62,f66,f70,f74,f78,f100,f108,f112,f130,f145,f146])).

fof(f146,plain,
    ( sK1 != sK3
    | r2_orders_2(sK0,sK3,sK2)
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    introduced(theory_axiom,[])).

fof(f145,plain,
    ( spl6_28
    | ~ spl6_4
    | ~ spl6_6
    | spl6_13
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f136,f128,f76,f68,f56,f52,f143])).

fof(f143,plain,
    ( spl6_28
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f52,plain,
    ( spl6_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f56,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f68,plain,
    ( spl6_13
  <=> ~ r2_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f76,plain,
    ( spl6_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f128,plain,
    ( spl6_26
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f136,plain,
    ( sK1 = sK3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f135,f69])).

fof(f69,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f68])).

fof(f135,plain,
    ( sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f134,f53])).

fof(f53,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f134,plain,
    ( ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f133,f57])).

fof(f57,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f133,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ spl6_16
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f131,f77])).

fof(f77,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f76])).

fof(f131,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ spl6_26 ),
    inference(resolution,[],[f129,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t29_orders_2.p',d10_orders_2)).

fof(f129,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl6_26
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f126,f106,f98,f76,f72,f56,f52,f44,f128])).

fof(f44,plain,
    ( spl6_0
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f72,plain,
    ( spl6_14
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f98,plain,
    ( spl6_18
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f106,plain,
    ( spl6_22
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f126,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f125,f57])).

fof(f125,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(resolution,[],[f118,f107])).

fof(f107,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f106])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f45,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f44])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f116,f73])).

fof(f73,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f72])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f115,f77])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f114,f53])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl6_18 ),
    inference(resolution,[],[f99,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t29_orders_2.p',t26_orders_2)).

fof(f99,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f98])).

fof(f112,plain,
    ( ~ spl6_25
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f96,f72,f64,f56,f52,f48,f110])).

fof(f110,plain,
    ( spl6_25
  <=> ~ r2_orders_2(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f48,plain,
    ( spl6_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f64,plain,
    ( spl6_10
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f96,plain,
    ( ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f49,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f95,plain,
    ( ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f94,f57])).

fof(f94,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f93,f73])).

fof(f93,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f89,f53])).

fof(f89,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f65,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t29_orders_2.p',t28_orders_2)).

fof(f65,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f64])).

fof(f108,plain,
    ( spl6_22
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f92,f72,f64,f56,f52,f106])).

fof(f92,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f91,f53])).

fof(f91,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f90,f57])).

fof(f90,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f88,f73])).

fof(f88,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f65,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,
    ( spl6_18
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f83,f76,f72,f60,f52,f98])).

fof(f60,plain,
    ( spl6_8
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f83,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f82,f53])).

fof(f82,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f81,f73])).

fof(f81,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f79,f77])).

fof(f79,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f61,f37])).

fof(f61,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f78,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f28,f76])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & r2_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r2_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t29_orders_2.p',t29_orders_2)).

fof(f74,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f27,f72])).

fof(f27,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    ~ spl6_13 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f29,f44])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
