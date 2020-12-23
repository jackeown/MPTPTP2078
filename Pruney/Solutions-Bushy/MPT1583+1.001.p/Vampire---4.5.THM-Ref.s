%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1583+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:09 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 459 expanded)
%              Number of leaves         :   48 ( 223 expanded)
%              Depth                    :   10
%              Number of atoms          :  859 (2958 expanded)
%              Number of equality atoms :   25 ( 176 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f85,f86,f90,f94,f98,f102,f106,f110,f114,f118,f124,f129,f142,f147,f152,f162,f165,f176,f187,f190,f221,f230,f235,f253,f256,f265,f279,f297,f304,f307,f316,f318])).

fof(f318,plain,
    ( ~ spl7_39
    | spl7_10
    | ~ spl7_8
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f317,f314,f100,f108,f302])).

fof(f302,plain,
    ( spl7_39
  <=> m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f108,plain,
    ( spl7_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f100,plain,
    ( spl7_8
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f314,plain,
    ( spl7_41
  <=> ! [X0] :
        ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_yellow_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f317,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl7_8
    | ~ spl7_41 ),
    inference(resolution,[],[f315,f101])).

fof(f101,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ m1_yellow_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(X0)) )
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f314])).

fof(f316,plain,
    ( spl7_12
    | ~ spl7_11
    | spl7_41
    | spl7_38 ),
    inference(avatar_split_clause,[],[f312,f294,f314,f112,f116])).

fof(f116,plain,
    ( spl7_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f112,plain,
    ( spl7_11
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f294,plain,
    ( spl7_38
  <=> m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(X0))
        | ~ m1_yellow_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_38 ),
    inference(resolution,[],[f295,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_yellow_0)).

fof(f295,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | spl7_38 ),
    inference(avatar_component_clause,[],[f294])).

fof(f307,plain,
    ( ~ spl7_18
    | ~ spl7_14
    | spl7_16
    | spl7_39 ),
    inference(avatar_split_clause,[],[f305,f302,f145,f127,f156])).

fof(f156,plain,
    ( spl7_18
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f127,plain,
    ( spl7_14
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f145,plain,
    ( spl7_16
  <=> r2_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f305,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_39 ),
    inference(resolution,[],[f303,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f303,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | spl7_39 ),
    inference(avatar_component_clause,[],[f302])).

fof(f304,plain,
    ( ~ spl7_18
    | spl7_10
    | ~ spl7_39
    | spl7_37 ),
    inference(avatar_split_clause,[],[f300,f291,f302,f108,f156])).

fof(f291,plain,
    ( spl7_37
  <=> r2_hidden(sK5(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f300,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | spl7_37 ),
    inference(resolution,[],[f292,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f130,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f68,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f292,plain,
    ( ~ r2_hidden(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | spl7_37 ),
    inference(avatar_component_clause,[],[f291])).

fof(f297,plain,
    ( ~ spl7_37
    | ~ spl7_38
    | spl7_16
    | ~ spl7_19
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f289,f233,f160,f145,f294,f291])).

fof(f160,plain,
    ( spl7_19
  <=> r2_hidden(sK5(sK1,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

% (26009)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f233,plain,
    ( spl7_30
  <=> ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK3),u1_struct_0(sK1))
        | r2_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK5(sK1,X0,sK3),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK1,X0,sK3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f289,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl7_19
    | ~ spl7_30 ),
    inference(resolution,[],[f234,f161])).

fof(f161,plain,
    ( r2_hidden(sK5(sK1,sK2,sK3),sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK3),sK2)
        | r2_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK5(sK1,X0,sK3),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK1,X0,sK3),u1_struct_0(sK1)) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f233])).

fof(f279,plain,
    ( ~ spl7_31
    | spl7_10
    | ~ spl7_8
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f278,f263,f100,f108,f247])).

fof(f247,plain,
    ( spl7_31
  <=> m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f263,plain,
    ( spl7_34
  <=> ! [X0] :
        ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_yellow_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f278,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl7_8
    | ~ spl7_34 ),
    inference(resolution,[],[f264,f101])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ m1_yellow_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(X0)) )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( spl7_12
    | ~ spl7_11
    | spl7_34
    | spl7_32 ),
    inference(avatar_split_clause,[],[f261,f250,f263,f112,f116])).

fof(f250,plain,
    ( spl7_32
  <=> m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(X0))
        | ~ m1_yellow_0(X0,sK0)
        | v2_struct_0(X0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl7_32 ),
    inference(resolution,[],[f251,f66])).

fof(f251,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | spl7_32 ),
    inference(avatar_component_clause,[],[f250])).

fof(f256,plain,
    ( ~ spl7_18
    | ~ spl7_14
    | spl7_13
    | spl7_31 ),
    inference(avatar_split_clause,[],[f254,f247,f122,f127,f156])).

fof(f122,plain,
    ( spl7_13
  <=> r1_lattice3(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f254,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_31 ),
    inference(resolution,[],[f248,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

% (26027)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f38,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f248,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f247])).

fof(f253,plain,
    ( ~ spl7_18
    | ~ spl7_14
    | ~ spl7_31
    | ~ spl7_32
    | spl7_13
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f245,f228,f122,f250,f247,f127,f156])).

fof(f228,plain,
    ( spl7_29
  <=> ! [X0] :
        ( ~ r2_hidden(sK6(sK1,X0,sK3),sK2)
        | r1_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f245,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl7_29 ),
    inference(duplicate_literal_removal,[],[f244])).

fof(f244,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | r1_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl7_29 ),
    inference(resolution,[],[f229,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK1,X0,sK3),sK2)
        | r1_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK1)) )
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f228])).

fof(f235,plain,
    ( ~ spl7_18
    | ~ spl7_14
    | spl7_30
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f231,f219,f233,f127,f156])).

fof(f219,plain,
    ( spl7_27
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK1,X0,sK3),u1_struct_0(sK1))
        | ~ r2_hidden(sK5(sK1,X0,sK3),sK2)
        | ~ m1_subset_1(sK5(sK1,X0,sK3),u1_struct_0(sK0))
        | r2_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl7_27 ),
    inference(resolution,[],[f220,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f220,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,X0,sK3)
        | ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f219])).

fof(f230,plain,
    ( ~ spl7_18
    | ~ spl7_14
    | spl7_29
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f226,f185,f228,f127,f156])).

fof(f185,plain,
    ( spl7_23
  <=> ! [X0] :
        ( r1_orders_2(sK1,sK3,X0)
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK1,X0,sK3),sK2)
        | ~ m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK1,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl7_23 ),
    inference(resolution,[],[f186,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f186,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3,X0)
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f221,plain,
    ( ~ spl7_14
    | ~ spl7_7
    | spl7_27
    | ~ spl7_17
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f217,f174,f150,f219,f96,f127])).

fof(f96,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f150,plain,
    ( spl7_17
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f174,plain,
    ( spl7_21
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK1)) )
    | ~ spl7_17
    | ~ spl7_21 ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK1)) )
    | ~ spl7_17
    | ~ spl7_21 ),
    inference(resolution,[],[f151,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK1)) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f151,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f150])).

fof(f190,plain,
    ( ~ spl7_18
    | spl7_10
    | ~ spl7_14
    | spl7_22 ),
    inference(avatar_split_clause,[],[f188,f182,f127,f108,f156])).

fof(f182,plain,
    ( spl7_22
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f188,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | spl7_22 ),
    inference(resolution,[],[f183,f131])).

fof(f183,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f187,plain,
    ( ~ spl7_22
    | ~ spl7_7
    | spl7_23
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f180,f174,f140,f185,f96,f182])).

fof(f140,plain,
    ( spl7_15
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f180,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(sK3,u1_struct_0(sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(sK3,u1_struct_0(sK1))
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(resolution,[],[f175,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3,X0)
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f176,plain,
    ( ~ spl7_11
    | ~ spl7_8
    | spl7_21
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f171,f104,f174,f100,f112])).

fof(f104,plain,
    ( spl7_9
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_yellow_0(sK1,sK0)
        | r1_orders_2(sK1,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f119,f105])).

fof(f105,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f119,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f70,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).

fof(f165,plain,
    ( ~ spl7_11
    | ~ spl7_8
    | spl7_18 ),
    inference(avatar_split_clause,[],[f164,f156,f100,f112])).

fof(f164,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_8
    | spl7_18 ),
    inference(resolution,[],[f163,f101])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_yellow_0(sK1,X0)
        | ~ l1_orders_2(X0) )
    | spl7_18 ),
    inference(resolution,[],[f157,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f157,plain,
    ( ~ l1_orders_2(sK1)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f162,plain,
    ( ~ spl7_18
    | ~ spl7_14
    | spl7_19
    | spl7_16 ),
    inference(avatar_split_clause,[],[f154,f145,f160,f127,f156])).

fof(f154,plain,
    ( r2_hidden(sK5(sK1,sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_16 ),
    inference(resolution,[],[f146,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f146,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f152,plain,
    ( ~ spl7_11
    | ~ spl7_7
    | spl7_17
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f148,f83,f150,f96,f112])).

fof(f83,plain,
    ( spl7_4
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f147,plain,
    ( ~ spl7_16
    | spl7_2
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f143,f88,f75,f145])).

fof(f75,plain,
    ( spl7_2
  <=> r2_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f88,plain,
    ( spl7_5
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f143,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | spl7_2
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f76,f89])).

fof(f89,plain,
    ( sK3 = sK4
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f76,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f142,plain,
    ( ~ spl7_11
    | ~ spl7_7
    | spl7_15
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f136,f79,f140,f96,f112])).

fof(f79,plain,
    ( spl7_3
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f61,f80])).

fof(f80,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f129,plain,
    ( spl7_14
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f125,f92,f88,f127])).

fof(f92,plain,
    ( spl7_6
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f125,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(superposition,[],[f93,f89])).

fof(f93,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f124,plain,
    ( ~ spl7_13
    | spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f120,f88,f72,f122])).

fof(f72,plain,
    ( spl7_1
  <=> r1_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f120,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | spl7_1
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f73,f89])).

fof(f73,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f118,plain,(
    ~ spl7_12 ),
    inference(avatar_split_clause,[],[f42,f116])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ( ~ r2_lattice3(sK1,sK2,sK4)
        & r2_lattice3(sK0,sK2,sK3) )
      | ( ~ r1_lattice3(sK1,sK2,sK4)
        & r1_lattice3(sK0,sK2,sK3) ) )
    & sK3 = sK4
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
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
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(sK0,X2,X3) )
                    | ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(sK0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ( ( ~ r2_lattice3(X1,X2,X4)
                    & r2_lattice3(sK0,X2,X3) )
                  | ( ~ r1_lattice3(X1,X2,X4)
                    & r1_lattice3(sK0,X2,X3) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_yellow_0(X1,sK0)
        & v4_yellow_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ( ( ~ r2_lattice3(sK1,X2,X4)
                  & r2_lattice3(sK0,X2,X3) )
                | ( ~ r1_lattice3(sK1,X2,X4)
                  & r1_lattice3(sK0,X2,X3) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_yellow_0(sK1,sK0)
      & v4_yellow_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ( ( ~ r2_lattice3(sK1,X2,X4)
                & r2_lattice3(sK0,X2,X3) )
              | ( ~ r1_lattice3(sK1,X2,X4)
                & r1_lattice3(sK0,X2,X3) ) )
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ( ( ~ r2_lattice3(sK1,sK2,X4)
              & r2_lattice3(sK0,sK2,sK3) )
            | ( ~ r1_lattice3(sK1,sK2,X4)
              & r1_lattice3(sK0,sK2,sK3) ) )
          & sK3 = X4
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ( ( ~ r2_lattice3(sK1,sK2,X4)
            & r2_lattice3(sK0,sK2,sK3) )
          | ( ~ r1_lattice3(sK1,sK2,X4)
            & r1_lattice3(sK0,sK2,sK3) ) )
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ( ( ~ r2_lattice3(sK1,sK2,sK4)
          & r2_lattice3(sK0,sK2,sK3) )
        | ( ~ r1_lattice3(sK1,sK2,sK4)
          & r1_lattice3(sK0,sK2,sK3) ) )
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_yellow_0)).

fof(f114,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f43,f112])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f110,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f44,f108])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f45,f104])).

fof(f45,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f46,f100])).

fof(f46,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f50,f83,f79])).

fof(f50,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f51,f83,f72])).

fof(f51,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f52,f75,f79])).

fof(f52,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f53,f75,f72])).

fof(f53,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4)
    | ~ r1_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
