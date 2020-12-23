%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f48,f52,f56,f60,f64,f86,f94,f98,f116,f131,f132])).

fof(f132,plain,
    ( sK1 != sK3
    | r2_orders_2(sK0,sK3,sK2)
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f131,plain,
    ( spl4_15
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f122,f114,f62,f54,f42,f38,f129])).

fof(f129,plain,
    ( spl4_15
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f38,plain,
    ( spl4_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f42,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f54,plain,
    ( spl4_7
  <=> r2_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f62,plain,
    ( spl4_9
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f114,plain,
    ( spl4_14
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f122,plain,
    ( sK1 = sK3
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f121,f55])).

fof(f55,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f121,plain,
    ( sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f120,f39])).

fof(f39,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f120,plain,
    ( ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f43,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f119,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f117,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f117,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ spl4_14 ),
    inference(resolution,[],[f115,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f115,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl4_14
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f112,f92,f84,f62,f58,f42,f38,f30,f114])).

fof(f30,plain,
    ( spl4_1
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f58,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f84,plain,
    ( spl4_10
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f92,plain,
    ( spl4_12
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f112,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f111,f43])).

fof(f111,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(resolution,[],[f104,f93])).

fof(f93,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f103,f31])).

fof(f31,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f102,f59])).

fof(f59,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f101,f63])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f100,f39])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f85,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f85,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f98,plain,
    ( ~ spl4_13
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f82,f58,f50,f42,f38,f34,f96])).

fof(f96,plain,
    ( spl4_13
  <=> r2_orders_2(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f34,plain,
    ( spl4_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f50,plain,
    ( spl4_6
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f82,plain,
    ( ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f35,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f81,plain,
    ( ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f80,f43])).

fof(f80,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f79,f59])).

fof(f79,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f75,f39])).

fof(f75,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f51,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_orders_2)).

fof(f51,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f94,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f78,f58,f50,f42,f38,f92])).

fof(f78,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f77,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f76,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f74,f59])).

fof(f74,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f51,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f69,f62,f58,f46,f38,f84])).

fof(f46,plain,
    ( spl4_5
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f69,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f68,f39])).

fof(f68,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f67,f59])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f65,f63])).

fof(f65,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f47,f24])).

fof(f47,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f64,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f18,f62])).

fof(f18,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_orders_2)).

fof(f60,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f17,f58])).

fof(f17,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f16,f54])).

fof(f16,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f15,f50])).

fof(f15,plain,(
    r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f14,f46])).

fof(f14,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f13,f42])).

fof(f13,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:49:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (25440)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (25455)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (25447)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (25440)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f48,f52,f56,f60,f64,f86,f94,f98,f116,f131,f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    sK1 != sK3 | r2_orders_2(sK0,sK3,sK2) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl4_15 | ~spl4_3 | ~spl4_4 | spl4_7 | ~spl4_9 | ~spl4_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f122,f114,f62,f54,f42,f38,f129])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    spl4_15 <=> sK1 = sK3),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    spl4_3 <=> l1_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl4_4 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl4_7 <=> r2_orders_2(sK0,sK1,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl4_9 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    spl4_14 <=> r1_orders_2(sK0,sK1,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    sK1 = sK3 | (~spl4_3 | ~spl4_4 | spl4_7 | ~spl4_9 | ~spl4_14)),
% 0.22/0.48    inference(subsumption_resolution,[],[f121,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ~r2_orders_2(sK0,sK1,sK3) | spl4_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f54])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    sK1 = sK3 | r2_orders_2(sK0,sK1,sK3) | (~spl4_3 | ~spl4_4 | ~spl4_9 | ~spl4_14)),
% 0.22/0.48    inference(subsumption_resolution,[],[f120,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    l1_orders_2(sK0) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f38])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ~l1_orders_2(sK0) | sK1 = sK3 | r2_orders_2(sK0,sK1,sK3) | (~spl4_4 | ~spl4_9 | ~spl4_14)),
% 0.22/0.48    inference(subsumption_resolution,[],[f119,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK3 | r2_orders_2(sK0,sK1,sK3) | (~spl4_9 | ~spl4_14)),
% 0.22/0.48    inference(subsumption_resolution,[],[f117,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | sK1 = sK3 | r2_orders_2(sK0,sK1,sK3) | ~spl4_14),
% 0.22/0.48    inference(resolution,[],[f115,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2 | r2_orders_2(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK1,sK3) | ~spl4_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f114])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl4_14 | ~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f112,f92,f84,f62,f58,f42,f38,f30,f114])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    spl4_1 <=> v4_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl4_8 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl4_10 <=> r1_orders_2(sK0,sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    spl4_12 <=> r1_orders_2(sK0,sK2,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK1,sK3) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_12)),
% 0.22/0.48    inference(subsumption_resolution,[],[f111,f43])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK3) | (~spl4_1 | ~spl4_3 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_12)),
% 0.22/0.48    inference(resolution,[],[f104,f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK2,sK3) | ~spl4_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f92])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0)) ) | (~spl4_1 | ~spl4_3 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f103,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    v4_orders_2(sK0) | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f30])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) ) | (~spl4_3 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f102,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) ) | (~spl4_3 | ~spl4_9 | ~spl4_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f101,f63])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) ) | (~spl4_3 | ~spl4_10)),
% 0.22/0.48    inference(subsumption_resolution,[],[f100,f39])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0)) ) | ~spl4_10),
% 0.22/0.48    inference(resolution,[],[f85,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_orders_2(X0,X1,X3) | (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK1,sK2) | ~spl4_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ~spl4_13 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f82,f58,f50,f42,f38,f34,f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    spl4_13 <=> r2_orders_2(sK0,sK3,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl4_2 <=> v5_orders_2(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl4_6 <=> r2_orders_2(sK0,sK2,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ~r2_orders_2(sK0,sK3,sK2) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v5_orders_2(sK0) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f34])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ~v5_orders_2(sK0) | ~r2_orders_2(sK0,sK3,sK2) | (~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f80,f43])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r2_orders_2(sK0,sK3,sK2) | (~spl4_3 | ~spl4_6 | ~spl4_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f79,f59])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r2_orders_2(sK0,sK3,sK2) | (~spl4_3 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f75,f39])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~r2_orders_2(sK0,sK3,sK2) | ~spl4_6),
% 0.22/0.48    inference(resolution,[],[f51,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_orders_2(X0,X2,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r2_orders_2(X0,X1,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_orders_2)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    r2_orders_2(sK0,sK2,sK3) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl4_12 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f78,f58,f50,f42,f38,f92])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK2,sK3) | (~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f77,f39])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK2,sK3) | ~l1_orders_2(sK0) | (~spl4_4 | ~spl4_6 | ~spl4_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f76,f43])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3) | ~l1_orders_2(sK0) | (~spl4_6 | ~spl4_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f59])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3) | ~l1_orders_2(sK0) | ~spl4_6),
% 0.22/0.48    inference(resolution,[],[f51,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl4_10 | ~spl4_3 | ~spl4_5 | ~spl4_8 | ~spl4_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f69,f62,f58,f46,f38,f84])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl4_5 <=> r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK1,sK2) | (~spl4_3 | ~spl4_5 | ~spl4_8 | ~spl4_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f39])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | (~spl4_5 | ~spl4_8 | ~spl4_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f67,f59])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | (~spl4_5 | ~spl4_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f65,f63])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~spl4_5),
% 0.22/0.48    inference(resolution,[],[f47,f24])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    r2_orders_2(sK0,sK1,sK2) | ~spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl4_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f62])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(X0,X1,X3) & r2_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_orders_2(X0,X1,X3) & (r2_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)) => r2_orders_2(X0,X1,X3))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)) => r2_orders_2(X0,X1,X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_orders_2)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f58])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ~spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f16,f54])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ~r2_orders_2(sK0,sK1,sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f15,f50])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    r2_orders_2(sK0,sK2,sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f14,f46])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f13,f42])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f38])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    l1_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f34])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    v5_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f30])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    v4_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (25440)------------------------------
% 0.22/0.48  % (25440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (25440)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (25440)Memory used [KB]: 6140
% 0.22/0.48  % (25440)Time elapsed: 0.046 s
% 0.22/0.48  % (25440)------------------------------
% 0.22/0.48  % (25440)------------------------------
% 0.22/0.48  % (25439)Success in time 0.114 s
%------------------------------------------------------------------------------
