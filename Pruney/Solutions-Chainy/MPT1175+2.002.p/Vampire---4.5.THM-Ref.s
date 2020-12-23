%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 176 expanded)
%              Number of leaves         :   22 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  308 (1024 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f71,f75,f79,f85,f233,f242,f257,f262])).

fof(f262,plain,
    ( ~ spl5_24
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f259,f255,f83,f239])).

fof(f239,plain,
    ( spl5_24
  <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f83,plain,
    ( spl5_10
  <=> sK2 = k4_xboole_0(k2_xboole_0(sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f255,plain,
    ( spl5_26
  <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f259,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl5_10
    | ~ spl5_26 ),
    inference(resolution,[],[f256,f87])).

fof(f87,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl5_10 ),
    inference(superposition,[],[f42,f84])).

fof(f84,plain,
    ( sK2 = k4_xboole_0(k2_xboole_0(sK2,sK3),sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f256,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( spl5_26
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f235,f231,f57,f49,f255])).

fof(f49,plain,
    ( spl5_2
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f57,plain,
    ( spl5_4
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f231,plain,
    ( spl5_23
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f235,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_23 ),
    inference(resolution,[],[f234,f50])).

fof(f50,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) )
    | ~ spl5_4
    | ~ spl5_23 ),
    inference(resolution,[],[f232,f58])).

fof(f58,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ m2_orders_2(X0,sK0,X1) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f231])).

fof(f242,plain,
    ( spl5_24
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f236,f231,f57,f53,f239])).

fof(f53,plain,
    ( spl5_3
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f236,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_23 ),
    inference(resolution,[],[f234,f54])).

fof(f54,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f233,plain,
    ( spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | spl5_23
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f225,f61,f231,f65,f69,f73,f77])).

fof(f77,plain,
    ( spl5_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f73,plain,
    ( spl5_8
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f69,plain,
    ( spl5_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f65,plain,
    ( spl5_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f61,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f32,f62])).

fof(f62,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(f85,plain,
    ( spl5_10
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f80,f45,f83])).

fof(f45,plain,
    ( spl5_1
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,
    ( sK2 = k4_xboole_0(k2_xboole_0(sK2,sK3),sK3)
    | ~ spl5_1 ),
    inference(resolution,[],[f34,f46])).

fof(f46,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f79,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f23,f77])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( r1_xboole_0(sK2,sK3)
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( r1_xboole_0(X2,X3)
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(X2,X3)
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( r1_xboole_0(X2,X3)
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( r1_xboole_0(X2,X3)
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( r1_xboole_0(X2,X3)
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( r1_xboole_0(sK2,X3)
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( r1_xboole_0(sK2,X3)
        & m2_orders_2(X3,sK0,sK1) )
   => ( r1_xboole_0(sK2,sK3)
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(X2,X3)
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(X2,X3)
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).

fof(f75,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f25,f69])).

fof(f25,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f45])).

fof(f31,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (23140)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (23148)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (23139)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (23140)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (23142)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (23147)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f67,f71,f75,f79,f85,f233,f242,f257,f262])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    ~spl5_24 | ~spl5_10 | ~spl5_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f259,f255,f83,f239])).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    spl5_24 <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl5_10 <=> sK2 = k4_xboole_0(k2_xboole_0(sK2,sK3),sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    spl5_26 <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    ~r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) | (~spl5_10 | ~spl5_26)),
% 0.22/0.52    inference(resolution,[],[f256,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(X1,sK3) | ~r2_hidden(X1,sK2)) ) | ~spl5_10),
% 0.22/0.52    inference(superposition,[],[f42,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    sK2 = k4_xboole_0(k2_xboole_0(sK2,sK3),sK3) | ~spl5_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f83])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3) | ~spl5_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f255])).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    spl5_26 | ~spl5_2 | ~spl5_4 | ~spl5_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f235,f231,f57,f49,f255])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    spl5_2 <=> m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl5_4 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    spl5_23 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3) | (~spl5_2 | ~spl5_4 | ~spl5_23)),
% 0.22/0.52    inference(resolution,[],[f234,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    m2_orders_2(sK3,sK0,sK1) | ~spl5_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f49])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)) ) | (~spl5_4 | ~spl5_23)),
% 0.22/0.52    inference(resolution,[],[f232,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl5_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f57])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~m2_orders_2(X0,sK0,X1)) ) | ~spl5_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f231])).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    spl5_24 | ~spl5_3 | ~spl5_4 | ~spl5_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f236,f231,f57,f53,f239])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    spl5_3 <=> m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) | (~spl5_3 | ~spl5_4 | ~spl5_23)),
% 0.22/0.52    inference(resolution,[],[f234,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    m2_orders_2(sK2,sK0,sK1) | ~spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f53])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    spl5_9 | ~spl5_8 | ~spl5_7 | ~spl5_6 | spl5_23 | ~spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f225,f61,f231,f65,f69,f73,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl5_9 <=> v2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl5_8 <=> v3_orders_2(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl5_7 <=> v4_orders_2(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl5_6 <=> v5_orders_2(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl5_5 <=> l1_orders_2(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 0.22/0.52    inference(resolution,[],[f32,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    l1_orders_2(sK0) | ~spl5_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f61])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    spl5_10 | ~spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f80,f45,f83])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    spl5_1 <=> r1_xboole_0(sK2,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    sK2 = k4_xboole_0(k2_xboole_0(sK2,sK3),sK3) | ~spl5_1),
% 0.22/0.52    inference(resolution,[],[f34,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    r1_xboole_0(sK2,sK3) | ~spl5_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f45])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ~spl5_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f23,f77])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    (((r1_xboole_0(sK2,sK3) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15,f14,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r1_xboole_0(X2,X3) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (r1_xboole_0(X2,X3) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : (? [X3] : (r1_xboole_0(X2,X3) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (r1_xboole_0(X2,X3) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X2] : (? [X3] : (r1_xboole_0(X2,X3) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : (r1_xboole_0(sK2,X3) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X3] : (r1_xboole_0(sK2,X3) & m2_orders_2(X3,sK0,sK1)) => (r1_xboole_0(sK2,sK3) & m2_orders_2(sK3,sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r1_xboole_0(X2,X3) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (r1_xboole_0(X2,X3) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl5_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f73])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    v3_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl5_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f25,f69])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    v4_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl5_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f65])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v5_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl5_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f61])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    spl5_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f57])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl5_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f53])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f30,f49])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f31,f45])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    r1_xboole_0(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23140)------------------------------
% 0.22/0.52  % (23140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23140)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23140)Memory used [KB]: 10746
% 0.22/0.52  % (23140)Time elapsed: 0.069 s
% 0.22/0.52  % (23140)------------------------------
% 0.22/0.52  % (23140)------------------------------
% 0.22/0.52  % (23133)Success in time 0.149 s
%------------------------------------------------------------------------------
