%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 147 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  335 ( 739 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f89,f93,f109,f111,f116,f139,f194,f208])).

fof(f208,plain,(
    ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl8_11 ),
    inference(resolution,[],[f138,f47])).

fof(f47,plain,(
    ~ r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_waybel_0(sK2,sK3,u1_struct_0(sK2))
    & l1_waybel_0(sK3,sK2)
    & v7_waybel_0(sK3)
    & v4_orders_2(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK2,X1,u1_struct_0(sK2))
          & l1_waybel_0(X1,sK2)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK2,X1,u1_struct_0(sK2))
        & l1_waybel_0(X1,sK2)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK2,sK3,u1_struct_0(sK2))
      & l1_waybel_0(sK3,sK2)
      & v7_waybel_0(sK3)
      & v4_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f138,plain,
    ( r1_waybel_0(sK2,sK3,u1_struct_0(sK2))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_11
  <=> r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f194,plain,
    ( ~ spl8_4
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f190,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f4,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f190,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f151,f91])).

fof(f91,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) != k2_tarski(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f66,f48])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f151,plain,
    ( ! [X0] :
        ( r2_hidden(k2_waybel_0(sK2,sK3,sK5(k1_xboole_0,sK3,sK2,X0)),k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f144,f55])).

fof(f55,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
              | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( ( r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0)
              & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5))
              & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1)) )
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
            | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0)
        & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5))
        & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( ? [X6] :
                ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
                & r1_orders_2(X1,X5,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ! [X3] :
          ( ? [X4] :
              ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              & r1_orders_2(X1,X3,X4)
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f144,plain,
    ( sP0(k1_xboole_0,sK3,sK2)
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(resolution,[],[f134,f95])).

fof(f95,plain,
    ( ! [X1] :
        ( ~ r2_waybel_0(sK2,sK3,X1)
        | sP0(X1,sK3,sK2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f88,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_waybel_0(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_waybel_0(X0,X1,X2)
            | ~ sP0(X2,X1,X0) )
          & ( sP0(X2,X1,X0)
            | ~ r2_waybel_0(X0,X1,X2) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_waybel_0(X0,X1,X2)
        <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f88,plain,
    ( sP1(sK2,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_4
  <=> sP1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f134,plain,
    ( r2_waybel_0(sK2,sK3,k1_xboole_0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_10
  <=> r2_waybel_0(sK2,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f139,plain,
    ( spl8_10
    | spl8_11
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f118,f114,f136,f132])).

fof(f114,plain,
    ( spl8_6
  <=> ! [X0] :
        ( r2_waybel_0(sK2,sK3,X0)
        | r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f118,plain,
    ( r1_waybel_0(sK2,sK3,u1_struct_0(sK2))
    | r2_waybel_0(sK2,sK3,k1_xboole_0)
    | ~ spl8_6 ),
    inference(superposition,[],[f115,f48])).

fof(f115,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0))
        | r2_waybel_0(sK2,sK3,X0) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl8_3
    | spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f112,f107,f114,f82])).

fof(f82,plain,
    ( spl8_3
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f107,plain,
    ( spl8_5
  <=> ! [X1,X0] :
        ( r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1))
        | r2_waybel_0(sK2,X0,X1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f112,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK2,sK3,X0)
        | v2_struct_0(sK3)
        | r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f108,f46])).

fof(f46,plain,(
    l1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK2)
        | r2_waybel_0(sK2,X0,X1)
        | v2_struct_0(X0)
        | r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1)) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f111,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl8_1 ),
    inference(resolution,[],[f75,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f109,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f105,f107,f73])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1))
      | ~ l1_waybel_0(X0,sK2)
      | v2_struct_0(X0)
      | r2_waybel_0(sK2,X0,X1)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f62,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f93,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl8_3 ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,
    ( v2_struct_0(sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f89,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f80,f77,f86,f82])).

fof(f77,plain,
    ( spl8_2
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK2)
        | sP1(sK2,X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f80,plain,
    ( sP1(sK2,sK3)
    | v2_struct_0(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f78,f46])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK2)
        | sP1(sK2,X0)
        | v2_struct_0(X0) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f71,f77,f73])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK2)
      | v2_struct_0(X0)
      | sP1(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | sP1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f21,f20])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (21946)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (21962)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (21938)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (21937)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (21946)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (21954)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f79,f89,f93,f109,f111,f116,f139,f194,f208])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    ~spl8_11),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f206])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    $false | ~spl8_11),
% 0.22/0.52    inference(resolution,[],[f138,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ~r1_waybel_0(sK2,sK3,u1_struct_0(sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    (~r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) & l1_waybel_0(sK3,sK2) & v7_waybel_0(sK3) & v4_orders_2(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f24,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK2,X1,u1_struct_0(sK2)) & l1_waybel_0(X1,sK2) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ? [X1] : (~r1_waybel_0(sK2,X1,u1_struct_0(sK2)) & l1_waybel_0(X1,sK2) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) & l1_waybel_0(sK3,sK2) & v7_waybel_0(sK3) & v4_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) | ~spl8_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f136])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    spl8_11 <=> r1_waybel_0(sK2,sK3,u1_struct_0(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ~spl8_4 | ~spl8_10),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    $false | (~spl8_4 | ~spl8_10)),
% 0.22/0.52    inference(resolution,[],[f190,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(sK6(X0),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : m1_subset_1(sK6(X0),X0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f4,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK6(X0),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3))) ) | (~spl8_4 | ~spl8_10)),
% 0.22/0.52    inference(resolution,[],[f151,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) != k2_tarski(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(superposition,[],[f66,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.52    inference(flattening,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k2_waybel_0(sK2,sK3,sK5(k1_xboole_0,sK3,sK2,X0)),k1_xboole_0) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (~spl8_4 | ~spl8_10)),
% 0.22/0.52    inference(resolution,[],[f144,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X2,X0,X5,X1] : (~sP0(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,sK4(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0) & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5)) & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f31,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,sK4(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0) & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5)) & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.22/0.52    inference(rectify,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X2,X1,X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    sP0(k1_xboole_0,sK3,sK2) | (~spl8_4 | ~spl8_10)),
% 0.22/0.52    inference(resolution,[],[f134,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_waybel_0(sK2,sK3,X1) | sP0(X1,sK3,sK2)) ) | ~spl8_4),
% 0.22/0.52    inference(resolution,[],[f88,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~sP1(X0,X1) | ~r2_waybel_0(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_waybel_0(X0,X1,X2))) | ~sP1(X0,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    sP1(sK2,sK3) | ~spl8_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl8_4 <=> sP1(sK2,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    r2_waybel_0(sK2,sK3,k1_xboole_0) | ~spl8_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    spl8_10 <=> r2_waybel_0(sK2,sK3,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    spl8_10 | spl8_11 | ~spl8_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f118,f114,f136,f132])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl8_6 <=> ! [X0] : (r2_waybel_0(sK2,sK3,X0) | r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) | r2_waybel_0(sK2,sK3,k1_xboole_0) | ~spl8_6),
% 0.22/0.52    inference(superposition,[],[f115,f48])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X0] : (r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0)) | r2_waybel_0(sK2,sK3,X0)) ) | ~spl8_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f114])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    spl8_3 | spl8_6 | ~spl8_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f112,f107,f114,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl8_3 <=> v2_struct_0(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    spl8_5 <=> ! [X1,X0] : (r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1)) | r2_waybel_0(sK2,X0,X1) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ( ! [X0] : (r2_waybel_0(sK2,sK3,X0) | v2_struct_0(sK3) | r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0))) ) | ~spl8_5),
% 0.22/0.52    inference(resolution,[],[f108,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    l1_waybel_0(sK3,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_waybel_0(X0,sK2) | r2_waybel_0(sK2,X0,X1) | v2_struct_0(X0) | r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1))) ) | ~spl8_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f107])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    ~spl8_1),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f110])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    $false | ~spl8_1),
% 0.22/0.52    inference(resolution,[],[f75,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ~v2_struct_0(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    v2_struct_0(sK2) | ~spl8_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl8_1 <=> v2_struct_0(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl8_1 | spl8_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f105,f107,f73])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1)) | ~l1_waybel_0(X0,sK2) | v2_struct_0(X0) | r2_waybel_0(sK2,X0,X1) | v2_struct_0(sK2)) )),
% 0.22/0.52    inference(resolution,[],[f69,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    l1_struct_0(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f50,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ~spl8_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    $false | ~spl8_3),
% 0.22/0.52    inference(resolution,[],[f84,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ~v2_struct_0(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    v2_struct_0(sK3) | ~spl8_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f82])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl8_3 | spl8_4 | ~spl8_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f80,f77,f86,f82])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl8_2 <=> ! [X0] : (~l1_waybel_0(X0,sK2) | sP1(sK2,X0) | v2_struct_0(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    sP1(sK2,sK3) | v2_struct_0(sK3) | ~spl8_2),
% 0.22/0.52    inference(resolution,[],[f78,f46])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_waybel_0(X0,sK2) | sP1(sK2,X0) | v2_struct_0(X0)) ) | ~spl8_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl8_1 | spl8_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f71,f77,f73])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_waybel_0(X0,sK2) | v2_struct_0(X0) | sP1(sK2,X0) | v2_struct_0(sK2)) )),
% 0.22/0.52    inference(resolution,[],[f58,f42])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | sP1(X0,X1) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(definition_folding,[],[f16,f21,f20])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (21946)------------------------------
% 0.22/0.52  % (21946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21946)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (21946)Memory used [KB]: 6268
% 0.22/0.52  % (21946)Time elapsed: 0.109 s
% 0.22/0.52  % (21946)------------------------------
% 0.22/0.52  % (21946)------------------------------
% 0.22/0.52  % (21933)Success in time 0.165 s
%------------------------------------------------------------------------------
