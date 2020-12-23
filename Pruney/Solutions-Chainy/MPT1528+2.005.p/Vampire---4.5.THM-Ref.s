%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 156 expanded)
%              Number of leaves         :   28 (  72 expanded)
%              Depth                    :    8
%              Number of atoms          :  362 ( 541 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f71,f79,f95,f111,f117,f123,f130,f135,f140,f145,f150,f155,f158,f161])).

fof(f161,plain,
    ( spl5_2
    | ~ spl5_18
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl5_2
    | ~ spl5_18
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f159,f122])).

fof(f122,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_18
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f159,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_21 ),
    inference(resolution,[],[f51,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_21
  <=> ! [X0] :
        ( r1_lattice3(sK0,X0,sK1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f51,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_2
  <=> r1_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f158,plain,
    ( spl5_1
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl5_1
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f156,f122])).

fof(f156,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_1
    | ~ spl5_24 ),
    inference(resolution,[],[f154,f47])).

fof(f47,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_1
  <=> r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f154,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_24
  <=> ! [X0] :
        ( r2_lattice3(sK0,X0,sK1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f155,plain,
    ( spl5_24
    | ~ spl5_16
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f151,f148,f109,f153])).

fof(f109,plain,
    ( spl5_16
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f148,plain,
    ( spl5_23
  <=> ! [X0] :
        ( r2_hidden(sK3(sK0,X0,sK1),X0)
        | r2_lattice3(sK0,X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f151,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_16
    | ~ spl5_23 ),
    inference(resolution,[],[f149,f110])).

fof(f110,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f149,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0,sK1),X0)
        | r2_lattice3(sK0,X0,sK1) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,
    ( spl5_23
    | ~ spl5_3
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f146,f143,f54,f148])).

fof(f54,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f143,plain,
    ( spl5_22
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f146,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0,sK1),X0)
        | r2_lattice3(sK0,X0,sK1) )
    | ~ spl5_3
    | ~ spl5_22 ),
    inference(resolution,[],[f144,f56])).

fof(f56,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK3(sK0,X0,X1),X0)
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f141,f93,f59,f143])).

fof(f59,plain,
    ( spl5_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f93,plain,
    ( spl5_12
  <=> ! [X1,X0,X2] :
        ( r2_lattice3(X0,X1,X2)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(resolution,[],[f94,f61])).

fof(f61,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(X0)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_lattice3(X0,X1,X2) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f140,plain,
    ( spl5_21
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f136,f133,f109,f138])).

fof(f133,plain,
    ( spl5_20
  <=> ! [X0] :
        ( r2_hidden(sK2(sK0,X0,sK1),X0)
        | r1_lattice3(sK0,X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f136,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(resolution,[],[f134,f110])).

fof(f134,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,X0,sK1),X0)
        | r1_lattice3(sK0,X0,sK1) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl5_20
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f131,f128,f54,f133])).

fof(f128,plain,
    ( spl5_19
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f131,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,X0,sK1),X0)
        | r1_lattice3(sK0,X0,sK1) )
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(resolution,[],[f129,f56])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK2(sK0,X0,X1),X0)
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl5_19
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f126,f77,f59,f128])).

fof(f77,plain,
    ( spl5_8
  <=> ! [X1,X0,X2] :
        ( r1_lattice3(X0,X1,X2)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(resolution,[],[f78,f61])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(X0)
        | r2_hidden(sK2(X0,X1,X2),X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_lattice3(X0,X1,X2) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f123,plain,
    ( spl5_18
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f118,f114,f64,f120])).

fof(f64,plain,
    ( spl5_5
  <=> v1_xboole_0(np__0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f114,plain,
    ( spl5_17
  <=> k1_xboole_0 = np__0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f118,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(superposition,[],[f66,f116])).

fof(f116,plain,
    ( k1_xboole_0 = np__0
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f66,plain,
    ( v1_xboole_0(np__0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f117,plain,
    ( spl5_17
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f112,f69,f64,f114])).

fof(f69,plain,
    ( spl5_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f112,plain,
    ( k1_xboole_0 = np__0
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f70,f66])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f111,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f42,f109])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f95,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f40,f93])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f79,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

% (24619)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% (24614)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f17,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f71,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f67,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f32,f64])).

fof(f32,plain,(
    v1_xboole_0(np__0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(np__0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc0_boole)).

fof(f62,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
      | ~ r2_lattice3(sK0,k1_xboole_0,sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
              | ~ r2_lattice3(X0,k1_xboole_0,X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_lattice3(sK0,k1_xboole_0,X1)
            | ~ r2_lattice3(sK0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ( ~ r1_lattice3(sK0,k1_xboole_0,X1)
          | ~ r2_lattice3(sK0,k1_xboole_0,X1) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,sK1) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r1_lattice3(X0,k1_xboole_0,X1)
              & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f57,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f31,f49,f45])).

fof(f31,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | ~ r2_lattice3(sK0,k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:41:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (24613)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (24615)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (24613)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f162,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f71,f79,f95,f111,f117,f123,f130,f135,f140,f145,f150,f155,f158,f161])).
% 0.22/0.43  fof(f161,plain,(
% 0.22/0.43    spl5_2 | ~spl5_18 | ~spl5_21),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f160])).
% 0.22/0.43  fof(f160,plain,(
% 0.22/0.43    $false | (spl5_2 | ~spl5_18 | ~spl5_21)),
% 0.22/0.43    inference(subsumption_resolution,[],[f159,f122])).
% 0.22/0.43  fof(f122,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | ~spl5_18),
% 0.22/0.43    inference(avatar_component_clause,[],[f120])).
% 0.22/0.43  fof(f120,plain,(
% 0.22/0.43    spl5_18 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.43  fof(f159,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_21)),
% 0.22/0.43    inference(resolution,[],[f51,f139])).
% 0.22/0.43  fof(f139,plain,(
% 0.22/0.43    ( ! [X0] : (r1_lattice3(sK0,X0,sK1) | ~v1_xboole_0(X0)) ) | ~spl5_21),
% 0.22/0.43    inference(avatar_component_clause,[],[f138])).
% 0.22/0.43  fof(f138,plain,(
% 0.22/0.43    spl5_21 <=> ! [X0] : (r1_lattice3(sK0,X0,sK1) | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ~r1_lattice3(sK0,k1_xboole_0,sK1) | spl5_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    spl5_2 <=> r1_lattice3(sK0,k1_xboole_0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.43  fof(f158,plain,(
% 0.22/0.43    spl5_1 | ~spl5_18 | ~spl5_24),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.43  fof(f157,plain,(
% 0.22/0.43    $false | (spl5_1 | ~spl5_18 | ~spl5_24)),
% 0.22/0.43    inference(subsumption_resolution,[],[f156,f122])).
% 0.22/0.43  fof(f156,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | (spl5_1 | ~spl5_24)),
% 0.22/0.43    inference(resolution,[],[f154,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ~r2_lattice3(sK0,k1_xboole_0,sK1) | spl5_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl5_1 <=> r2_lattice3(sK0,k1_xboole_0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.43  fof(f154,plain,(
% 0.22/0.43    ( ! [X0] : (r2_lattice3(sK0,X0,sK1) | ~v1_xboole_0(X0)) ) | ~spl5_24),
% 0.22/0.43    inference(avatar_component_clause,[],[f153])).
% 0.22/0.43  fof(f153,plain,(
% 0.22/0.43    spl5_24 <=> ! [X0] : (r2_lattice3(sK0,X0,sK1) | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.43  fof(f155,plain,(
% 0.22/0.43    spl5_24 | ~spl5_16 | ~spl5_23),
% 0.22/0.43    inference(avatar_split_clause,[],[f151,f148,f109,f153])).
% 0.22/0.43  fof(f109,plain,(
% 0.22/0.43    spl5_16 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.43  fof(f148,plain,(
% 0.22/0.43    spl5_23 <=> ! [X0] : (r2_hidden(sK3(sK0,X0,sK1),X0) | r2_lattice3(sK0,X0,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.43  fof(f151,plain,(
% 0.22/0.43    ( ! [X0] : (r2_lattice3(sK0,X0,sK1) | ~v1_xboole_0(X0)) ) | (~spl5_16 | ~spl5_23)),
% 0.22/0.43    inference(resolution,[],[f149,f110])).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl5_16),
% 0.22/0.43    inference(avatar_component_clause,[],[f109])).
% 0.22/0.43  fof(f149,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK3(sK0,X0,sK1),X0) | r2_lattice3(sK0,X0,sK1)) ) | ~spl5_23),
% 0.22/0.43    inference(avatar_component_clause,[],[f148])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    spl5_23 | ~spl5_3 | ~spl5_22),
% 0.22/0.43    inference(avatar_split_clause,[],[f146,f143,f54,f148])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl5_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.43  fof(f143,plain,(
% 0.22/0.43    spl5_22 <=> ! [X1,X0] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.43  fof(f146,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK3(sK0,X0,sK1),X0) | r2_lattice3(sK0,X0,sK1)) ) | (~spl5_3 | ~spl5_22)),
% 0.22/0.43    inference(resolution,[],[f144,f56])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f54])).
% 0.22/0.43  fof(f144,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,X0,X1),X0) | r2_lattice3(sK0,X0,X1)) ) | ~spl5_22),
% 0.22/0.43    inference(avatar_component_clause,[],[f143])).
% 0.22/0.43  fof(f145,plain,(
% 0.22/0.43    spl5_22 | ~spl5_4 | ~spl5_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f141,f93,f59,f143])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl5_4 <=> l1_orders_2(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.43  fof(f93,plain,(
% 0.22/0.43    spl5_12 <=> ! [X1,X0,X2] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.43  fof(f141,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | (~spl5_4 | ~spl5_12)),
% 0.22/0.43    inference(resolution,[],[f94,f61])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    l1_orders_2(sK0) | ~spl5_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f59])).
% 0.22/0.43  fof(f94,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) ) | ~spl5_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f93])).
% 0.22/0.43  fof(f140,plain,(
% 0.22/0.43    spl5_21 | ~spl5_16 | ~spl5_20),
% 0.22/0.43    inference(avatar_split_clause,[],[f136,f133,f109,f138])).
% 0.22/0.43  fof(f133,plain,(
% 0.22/0.43    spl5_20 <=> ! [X0] : (r2_hidden(sK2(sK0,X0,sK1),X0) | r1_lattice3(sK0,X0,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.43  fof(f136,plain,(
% 0.22/0.43    ( ! [X0] : (r1_lattice3(sK0,X0,sK1) | ~v1_xboole_0(X0)) ) | (~spl5_16 | ~spl5_20)),
% 0.22/0.43    inference(resolution,[],[f134,f110])).
% 0.22/0.43  fof(f134,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK2(sK0,X0,sK1),X0) | r1_lattice3(sK0,X0,sK1)) ) | ~spl5_20),
% 0.22/0.43    inference(avatar_component_clause,[],[f133])).
% 0.22/0.43  fof(f135,plain,(
% 0.22/0.43    spl5_20 | ~spl5_3 | ~spl5_19),
% 0.22/0.43    inference(avatar_split_clause,[],[f131,f128,f54,f133])).
% 0.22/0.43  fof(f128,plain,(
% 0.22/0.43    spl5_19 <=> ! [X1,X0] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.43  fof(f131,plain,(
% 0.22/0.43    ( ! [X0] : (r2_hidden(sK2(sK0,X0,sK1),X0) | r1_lattice3(sK0,X0,sK1)) ) | (~spl5_3 | ~spl5_19)),
% 0.22/0.43    inference(resolution,[],[f129,f56])).
% 0.22/0.43  fof(f129,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | r1_lattice3(sK0,X0,X1)) ) | ~spl5_19),
% 0.22/0.43    inference(avatar_component_clause,[],[f128])).
% 0.22/0.43  fof(f130,plain,(
% 0.22/0.43    spl5_19 | ~spl5_4 | ~spl5_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f126,f77,f59,f128])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl5_8 <=> ! [X1,X0,X2] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.43  fof(f126,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)) ) | (~spl5_4 | ~spl5_8)),
% 0.22/0.43    inference(resolution,[],[f78,f61])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) ) | ~spl5_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f77])).
% 0.22/0.43  fof(f123,plain,(
% 0.22/0.43    spl5_18 | ~spl5_5 | ~spl5_17),
% 0.22/0.43    inference(avatar_split_clause,[],[f118,f114,f64,f120])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl5_5 <=> v1_xboole_0(np__0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.43  fof(f114,plain,(
% 0.22/0.43    spl5_17 <=> k1_xboole_0 = np__0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0) | (~spl5_5 | ~spl5_17)),
% 0.22/0.43    inference(superposition,[],[f66,f116])).
% 0.22/0.43  fof(f116,plain,(
% 0.22/0.43    k1_xboole_0 = np__0 | ~spl5_17),
% 0.22/0.43    inference(avatar_component_clause,[],[f114])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    v1_xboole_0(np__0) | ~spl5_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f64])).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    spl5_17 | ~spl5_5 | ~spl5_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f112,f69,f64,f114])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl5_6 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.43  fof(f112,plain,(
% 0.22/0.43    k1_xboole_0 = np__0 | (~spl5_5 | ~spl5_6)),
% 0.22/0.43    inference(resolution,[],[f70,f66])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f69])).
% 0.22/0.43  fof(f111,plain,(
% 0.22/0.43    spl5_16),
% 0.22/0.43    inference(avatar_split_clause,[],[f42,f109])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(rectify,[],[f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    spl5_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f40,f93])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.43    inference(rectify,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.43    inference(nnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    spl5_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f36,f77])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.43    inference(rectify,[],[f17])).
% 0.22/0.43  % (24619)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.44  % (24614)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.44    inference(nnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.44    inference(flattening,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    spl5_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f33,f69])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl5_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f32,f64])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    v1_xboole_0(np__0)),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    v1_xboole_0(np__0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc0_boole)).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl5_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f29,f59])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    l1_orders_2(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ((~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : ((~r1_lattice3(sK0,k1_xboole_0,X1) | ~r2_lattice3(sK0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ? [X1] : ((~r1_lattice3(sK0,k1_xboole_0,X1) | ~r2_lattice3(sK0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.22/0.44    inference(negated_conjecture,[],[f6])).
% 0.22/0.44  fof(f6,conjecture,(
% 0.22/0.44    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    spl5_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f54])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    ~spl5_1 | ~spl5_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f31,f49,f45])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (24613)------------------------------
% 0.22/0.44  % (24613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (24613)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (24613)Memory used [KB]: 10618
% 0.22/0.44  % (24613)Time elapsed: 0.007 s
% 0.22/0.44  % (24613)------------------------------
% 0.22/0.44  % (24613)------------------------------
% 0.22/0.44  % (24607)Success in time 0.077 s
%------------------------------------------------------------------------------
