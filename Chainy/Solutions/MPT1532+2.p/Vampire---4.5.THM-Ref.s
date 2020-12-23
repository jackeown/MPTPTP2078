%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1532+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 6.96s
% Output     : Refutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 377 expanded)
%              Number of leaves         :   27 ( 168 expanded)
%              Depth                    :   10
%              Number of atoms          :  525 (1986 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6389,f6394,f6399,f6404,f6405,f6406,f6411,f6412,f6413,f6418,f6423,f6697,f6702,f6707,f6855,f6860,f6865,f13690,f13887,f13892,f14522,f15256,f15286])).

fof(f15286,plain,
    ( ~ spl406_3
    | ~ spl406_7
    | ~ spl406_8
    | spl406_37
    | ~ spl406_39
    | ~ spl406_622 ),
    inference(avatar_contradiction_clause,[],[f15285])).

fof(f15285,plain,
    ( $false
    | ~ spl406_3
    | ~ spl406_7
    | ~ spl406_8
    | spl406_37
    | ~ spl406_39
    | ~ spl406_622 ),
    inference(subsumption_resolution,[],[f15276,f14519])).

fof(f14519,plain,
    ( r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | ~ spl406_622 ),
    inference(avatar_component_clause,[],[f14517])).

fof(f14517,plain,
    ( spl406_622
  <=> r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_622])])).

fof(f15276,plain,
    ( ~ r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | ~ spl406_3
    | ~ spl406_7
    | ~ spl406_8
    | spl406_37
    | ~ spl406_39 ),
    inference(unit_resulting_resolution,[],[f6422,f6696,f6706,f6417,f6393,f4324])).

fof(f4324,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3782])).

fof(f3782,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
                & r2_hidden(sK7(X0,X1,X2),X1)
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3780,f3781])).

fof(f3781,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3780,plain,(
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
    inference(rectify,[],[f3779])).

fof(f3779,plain,(
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
    inference(nnf_transformation,[],[f3031])).

fof(f3031,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3030])).

fof(f3030,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2831])).

fof(f2831,axiom,(
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

fof(f6393,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl406_3 ),
    inference(avatar_component_clause,[],[f6391])).

fof(f6391,plain,
    ( spl406_3
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_3])])).

fof(f6417,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl406_7 ),
    inference(avatar_component_clause,[],[f6415])).

fof(f6415,plain,
    ( spl406_7
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_7])])).

fof(f6706,plain,
    ( m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0))
    | ~ spl406_39 ),
    inference(avatar_component_clause,[],[f6704])).

fof(f6704,plain,
    ( spl406_39
  <=> m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_39])])).

fof(f6696,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,k2_xboole_0(sK1,sK2),sK3))
    | spl406_37 ),
    inference(avatar_component_clause,[],[f6694])).

fof(f6694,plain,
    ( spl406_37
  <=> r1_orders_2(sK0,sK3,sK7(sK0,k2_xboole_0(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_37])])).

fof(f6422,plain,
    ( l1_orders_2(sK0)
    | ~ spl406_8 ),
    inference(avatar_component_clause,[],[f6420])).

fof(f6420,plain,
    ( spl406_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_8])])).

fof(f15256,plain,
    ( spl406_568
    | ~ spl406_53
    | spl406_569 ),
    inference(avatar_split_clause,[],[f15255,f13889,f6857,f13884])).

fof(f13884,plain,
    ( spl406_568
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_568])])).

fof(f6857,plain,
    ( spl406_53
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_53])])).

fof(f13889,plain,
    ( spl406_569
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_569])])).

fof(f15255,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK1)
    | ~ spl406_53
    | spl406_569 ),
    inference(subsumption_resolution,[],[f14863,f13891])).

fof(f13891,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | spl406_569 ),
    inference(avatar_component_clause,[],[f13889])).

fof(f14863,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK1)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | ~ spl406_53 ),
    inference(resolution,[],[f6859,f5766])).

fof(f5766,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f4280])).

fof(f4280,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3776])).

fof(f3776,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3774,f3775])).

fof(f3775,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3774,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f3773])).

fof(f3773,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f3772])).

fof(f3772,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f6859,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2))
    | ~ spl406_53 ),
    inference(avatar_component_clause,[],[f6857])).

fof(f14522,plain,
    ( spl406_622
    | ~ spl406_38
    | spl406_548 ),
    inference(avatar_split_clause,[],[f14521,f13687,f6699,f14517])).

fof(f6699,plain,
    ( spl406_38
  <=> r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_38])])).

fof(f13687,plain,
    ( spl406_548
  <=> r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_548])])).

fof(f14521,plain,
    ( r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | ~ spl406_38
    | spl406_548 ),
    inference(subsumption_resolution,[],[f14172,f13689])).

fof(f13689,plain,
    ( ~ r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK1)
    | spl406_548 ),
    inference(avatar_component_clause,[],[f13687])).

fof(f14172,plain,
    ( r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK1)
    | r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | ~ spl406_38 ),
    inference(resolution,[],[f6701,f5766])).

fof(f6701,plain,
    ( r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2))
    | ~ spl406_38 ),
    inference(avatar_component_clause,[],[f6699])).

fof(f13892,plain,
    ( ~ spl406_569
    | ~ spl406_5
    | ~ spl406_7
    | ~ spl406_8
    | spl406_52
    | ~ spl406_54 ),
    inference(avatar_split_clause,[],[f13759,f6862,f6852,f6420,f6415,f6401,f13889])).

fof(f6401,plain,
    ( spl406_5
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_5])])).

fof(f6852,plain,
    ( spl406_52
  <=> r1_orders_2(sK0,sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_52])])).

fof(f6862,plain,
    ( spl406_54
  <=> m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_54])])).

fof(f13759,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK2)
    | ~ spl406_5
    | ~ spl406_7
    | ~ spl406_8
    | spl406_52
    | ~ spl406_54 ),
    inference(unit_resulting_resolution,[],[f6422,f6403,f6417,f6854,f6864,f4247])).

fof(f4247,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3771])).

fof(f3771,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3769,f3770])).

fof(f3770,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3769,plain,(
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
    inference(rectify,[],[f3768])).

fof(f3768,plain,(
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
    inference(nnf_transformation,[],[f2996])).

fof(f2996,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2995])).

fof(f2995,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2832])).

fof(f2832,axiom,(
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

fof(f6864,plain,
    ( m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0))
    | ~ spl406_54 ),
    inference(avatar_component_clause,[],[f6862])).

fof(f6854,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK3)
    | spl406_52 ),
    inference(avatar_component_clause,[],[f6852])).

fof(f6403,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl406_5 ),
    inference(avatar_component_clause,[],[f6401])).

fof(f13887,plain,
    ( ~ spl406_568
    | ~ spl406_6
    | ~ spl406_7
    | ~ spl406_8
    | spl406_52
    | ~ spl406_54 ),
    inference(avatar_split_clause,[],[f13760,f6862,f6852,f6420,f6415,f6408,f13884])).

fof(f6408,plain,
    ( spl406_6
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_6])])).

fof(f13760,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK1)
    | ~ spl406_6
    | ~ spl406_7
    | ~ spl406_8
    | spl406_52
    | ~ spl406_54 ),
    inference(unit_resulting_resolution,[],[f6422,f6410,f6417,f6854,f6864,f4247])).

fof(f6410,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl406_6 ),
    inference(avatar_component_clause,[],[f6408])).

fof(f13690,plain,
    ( ~ spl406_548
    | ~ spl406_4
    | ~ spl406_7
    | ~ spl406_8
    | spl406_37
    | ~ spl406_39 ),
    inference(avatar_split_clause,[],[f13661,f6704,f6694,f6420,f6415,f6396,f13687])).

fof(f6396,plain,
    ( spl406_4
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_4])])).

fof(f13661,plain,
    ( ~ r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),sK1)
    | ~ spl406_4
    | ~ spl406_7
    | ~ spl406_8
    | spl406_37
    | ~ spl406_39 ),
    inference(unit_resulting_resolution,[],[f6422,f6398,f6417,f6696,f6706,f4324])).

fof(f6398,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl406_4 ),
    inference(avatar_component_clause,[],[f6396])).

fof(f6865,plain,
    ( spl406_54
    | spl406_2
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(avatar_split_clause,[],[f6840,f6420,f6415,f6386,f6862])).

fof(f6386,plain,
    ( spl406_2
  <=> r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_2])])).

fof(f6840,plain,
    ( m1_subset_1(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0))
    | spl406_2
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(unit_resulting_resolution,[],[f6422,f6417,f6388,f4248])).

fof(f4248,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3771])).

fof(f6388,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | spl406_2 ),
    inference(avatar_component_clause,[],[f6386])).

fof(f6860,plain,
    ( spl406_53
    | spl406_2
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(avatar_split_clause,[],[f6841,f6420,f6415,f6386,f6857])).

fof(f6841,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2))
    | spl406_2
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(unit_resulting_resolution,[],[f6422,f6417,f6388,f4249])).

fof(f4249,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3771])).

fof(f6855,plain,
    ( ~ spl406_52
    | spl406_2
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(avatar_split_clause,[],[f6842,f6420,f6415,f6386,f6852])).

fof(f6842,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,k2_xboole_0(sK1,sK2),sK3),sK3)
    | spl406_2
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(unit_resulting_resolution,[],[f6422,f6417,f6388,f4250])).

fof(f4250,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3771])).

fof(f6707,plain,
    ( spl406_39
    | spl406_1
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(avatar_split_clause,[],[f6688,f6420,f6415,f6382,f6704])).

fof(f6382,plain,
    ( spl406_1
  <=> r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl406_1])])).

fof(f6688,plain,
    ( m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),u1_struct_0(sK0))
    | spl406_1
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(unit_resulting_resolution,[],[f6422,f6417,f6384,f4325])).

fof(f4325,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3782])).

fof(f6384,plain,
    ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | spl406_1 ),
    inference(avatar_component_clause,[],[f6382])).

fof(f6702,plain,
    ( spl406_38
    | spl406_1
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(avatar_split_clause,[],[f6689,f6420,f6415,f6382,f6699])).

fof(f6689,plain,
    ( r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2),sK3),k2_xboole_0(sK1,sK2))
    | spl406_1
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(unit_resulting_resolution,[],[f6422,f6417,f6384,f4326])).

fof(f4326,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3782])).

fof(f6697,plain,
    ( ~ spl406_37
    | spl406_1
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(avatar_split_clause,[],[f6690,f6420,f6415,f6382,f6694])).

fof(f6690,plain,
    ( ~ r1_orders_2(sK0,sK3,sK7(sK0,k2_xboole_0(sK1,sK2),sK3))
    | spl406_1
    | ~ spl406_7
    | ~ spl406_8 ),
    inference(unit_resulting_resolution,[],[f6422,f6417,f6384,f4327])).

fof(f4327,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3782])).

fof(f6423,plain,(
    spl406_8 ),
    inference(avatar_split_clause,[],[f4230,f6420])).

fof(f4230,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3767])).

fof(f3767,plain,
    ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
        & r2_lattice3(sK0,sK2,sK3)
        & r2_lattice3(sK0,sK1,sK3) )
      | ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
        & r1_lattice3(sK0,sK2,sK3)
        & r1_lattice3(sK0,sK1,sK3) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2990,f3766,f3765])).

fof(f3765,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
                & r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
              | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
                & r1_lattice3(X0,X2,X3)
                & r1_lattice3(X0,X1,X3) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X3,X2,X1] :
          ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(sK0,X2,X3)
              & r2_lattice3(sK0,X1,X3) )
            | ( ~ r1_lattice3(sK0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(sK0,X2,X3)
              & r1_lattice3(sK0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3766,plain,
    ( ? [X3,X2,X1] :
        ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(X1,X2),X3)
            & r2_lattice3(sK0,X2,X3)
            & r2_lattice3(sK0,X1,X3) )
          | ( ~ r1_lattice3(sK0,k2_xboole_0(X1,X2),X3)
            & r1_lattice3(sK0,X2,X3)
            & r1_lattice3(sK0,X1,X3) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
          & r2_lattice3(sK0,sK2,sK3)
          & r2_lattice3(sK0,sK1,sK3) )
        | ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
          & r1_lattice3(sK0,sK2,sK3)
          & r1_lattice3(sK0,sK1,sK3) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2990,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(X0,X2,X3)
              & r1_lattice3(X0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f2989])).

fof(f2989,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(X0,X2,X3)
              & r1_lattice3(X0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2964])).

fof(f2964,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X0))
           => ( ( ( r2_lattice3(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3) )
               => r2_lattice3(X0,k2_xboole_0(X1,X2),X3) )
              & ( ( r1_lattice3(X0,X2,X3)
                  & r1_lattice3(X0,X1,X3) )
               => r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f2963])).

fof(f2963,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X0))
         => ( ( ( r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
             => r2_lattice3(X0,k2_xboole_0(X1,X2),X3) )
            & ( ( r1_lattice3(X0,X2,X3)
                & r1_lattice3(X0,X1,X3) )
             => r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_yellow_0)).

fof(f6418,plain,(
    spl406_7 ),
    inference(avatar_split_clause,[],[f4231,f6415])).

fof(f4231,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6413,plain,
    ( spl406_4
    | spl406_6 ),
    inference(avatar_split_clause,[],[f4232,f6408,f6396])).

fof(f4232,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6412,plain,
    ( spl406_3
    | spl406_6 ),
    inference(avatar_split_clause,[],[f4233,f6408,f6391])).

fof(f4233,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6411,plain,
    ( ~ spl406_1
    | spl406_6 ),
    inference(avatar_split_clause,[],[f4234,f6408,f6382])).

fof(f4234,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6406,plain,
    ( spl406_4
    | spl406_5 ),
    inference(avatar_split_clause,[],[f4235,f6401,f6396])).

fof(f4235,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6405,plain,
    ( spl406_3
    | spl406_5 ),
    inference(avatar_split_clause,[],[f4236,f6401,f6391])).

fof(f4236,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6404,plain,
    ( ~ spl406_1
    | spl406_5 ),
    inference(avatar_split_clause,[],[f4237,f6401,f6382])).

fof(f4237,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6399,plain,
    ( spl406_4
    | ~ spl406_2 ),
    inference(avatar_split_clause,[],[f4238,f6386,f6396])).

fof(f4238,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6394,plain,
    ( spl406_3
    | ~ spl406_2 ),
    inference(avatar_split_clause,[],[f4239,f6386,f6391])).

fof(f4239,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f3767])).

fof(f6389,plain,
    ( ~ spl406_1
    | ~ spl406_2 ),
    inference(avatar_split_clause,[],[f4240,f6386,f6382])).

fof(f4240,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3767])).
%------------------------------------------------------------------------------
