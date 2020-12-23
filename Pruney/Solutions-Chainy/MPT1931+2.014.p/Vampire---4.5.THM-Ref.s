%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 148 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  338 ( 740 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f98,f100,f115,f117,f122,f132,f134,f155])).

fof(f155,plain,
    ( ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f146,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f146,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f143,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f143,plain,
    ( r2_hidden(k2_waybel_0(sK2,sK3,sK5(k1_xboole_0,sK3,sK2,sK7(u1_struct_0(sK3)))),k1_xboole_0)
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f137,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f5,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r2_hidden(k2_waybel_0(sK2,sK3,sK5(k1_xboole_0,sK3,sK2,X0)),k1_xboole_0) )
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f135,f58])).

fof(f58,plain,(
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

fof(f135,plain,
    ( sP0(k1_xboole_0,sK3,sK2)
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(resolution,[],[f127,f102])).

fof(f102,plain,
    ( ! [X1] :
        ( ~ r2_waybel_0(sK2,sK3,X1)
        | sP0(X1,sK3,sK2) )
    | ~ spl9_4 ),
    inference(resolution,[],[f97,f54])).

fof(f54,plain,(
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

fof(f97,plain,
    ( sP1(sK2,sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl9_4
  <=> sP1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f127,plain,
    ( r2_waybel_0(sK2,sK3,k1_xboole_0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl9_7
  <=> r2_waybel_0(sK2,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f134,plain,(
    ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl9_8 ),
    inference(resolution,[],[f131,f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f24,f23])).

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

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f131,plain,
    ( r1_waybel_0(sK2,sK3,u1_struct_0(sK2))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl9_8
  <=> r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f132,plain,
    ( spl9_7
    | spl9_8
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f123,f120,f129,f125])).

fof(f120,plain,
    ( spl9_6
  <=> ! [X0] :
        ( r2_waybel_0(sK2,sK3,X0)
        | r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f123,plain,
    ( r1_waybel_0(sK2,sK3,u1_struct_0(sK2))
    | r2_waybel_0(sK2,sK3,k1_xboole_0)
    | ~ spl9_6 ),
    inference(superposition,[],[f121,f51])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f121,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0))
        | r2_waybel_0(sK2,sK3,X0) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl9_3
    | spl9_6
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f118,f113,f120,f91])).

fof(f91,plain,
    ( spl9_3
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f113,plain,
    ( spl9_5
  <=> ! [X1,X0] :
        ( r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1))
        | r2_waybel_0(sK2,X0,X1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f118,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK2,sK3,X0)
        | v2_struct_0(sK3)
        | r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0)) )
    | ~ spl9_5 ),
    inference(resolution,[],[f114,f48])).

fof(f48,plain,(
    l1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK2)
        | r2_waybel_0(sK2,X0,X1)
        | v2_struct_0(X0)
        | r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1)) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f117,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | ~ spl9_1 ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,
    ( v2_struct_0(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl9_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f115,plain,
    ( spl9_1
    | spl9_5 ),
    inference(avatar_split_clause,[],[f111,f113,f82])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1))
      | ~ l1_waybel_0(X0,sK2)
      | v2_struct_0(X0)
      | r2_waybel_0(sK2,X0,X1)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f65,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f100,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl9_3 ),
    inference(resolution,[],[f93,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,
    ( v2_struct_0(sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f98,plain,
    ( spl9_3
    | spl9_4
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f89,f86,f95,f91])).

fof(f86,plain,
    ( spl9_2
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK2)
        | sP1(sK2,X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f89,plain,
    ( sP1(sK2,sK3)
    | v2_struct_0(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f87,f48])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK2)
        | sP1(sK2,X0)
        | v2_struct_0(X0) )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f80,f86,f82])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK2)
      | v2_struct_0(X0)
      | sP1(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
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
    inference(definition_folding,[],[f17,f21,f20])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (12059)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (12059)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (12052)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f88,f98,f100,f115,f117,f122,f132,f134,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~spl9_4 | ~spl9_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    $false | (~spl9_4 | ~spl9_7)),
% 0.21/0.48    inference(resolution,[],[f146,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | (~spl9_4 | ~spl9_7)),
% 0.21/0.48    inference(resolution,[],[f143,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(rectify,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    r2_hidden(k2_waybel_0(sK2,sK3,sK5(k1_xboole_0,sK3,sK2,sK7(u1_struct_0(sK3)))),k1_xboole_0) | (~spl9_4 | ~spl9_7)),
% 0.21/0.48    inference(resolution,[],[f137,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(sK7(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0] : m1_subset_1(sK7(X0),X0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f5,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK7(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r2_hidden(k2_waybel_0(sK2,sK3,sK5(k1_xboole_0,sK3,sK2,X0)),k1_xboole_0)) ) | (~spl9_4 | ~spl9_7)),
% 0.21/0.48    inference(resolution,[],[f135,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X1] : (~sP0(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,sK4(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0) & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5)) & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f31,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,sK4(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X2,X1,sK5(X0,X1,X2,X5)),X0) & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5)) & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(rectify,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X2,X1,X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    sP0(k1_xboole_0,sK3,sK2) | (~spl9_4 | ~spl9_7)),
% 0.21/0.48    inference(resolution,[],[f127,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_waybel_0(sK2,sK3,X1) | sP0(X1,sK3,sK2)) ) | ~spl9_4),
% 0.21/0.48    inference(resolution,[],[f97,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP1(X0,X1) | ~r2_waybel_0(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_waybel_0(X0,X1,X2))) | ~sP1(X0,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    sP1(sK2,sK3) | ~spl9_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl9_4 <=> sP1(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    r2_waybel_0(sK2,sK3,k1_xboole_0) | ~spl9_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl9_7 <=> r2_waybel_0(sK2,sK3,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ~spl9_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    $false | ~spl9_8),
% 0.21/0.48    inference(resolution,[],[f131,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~r1_waybel_0(sK2,sK3,u1_struct_0(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    (~r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) & l1_waybel_0(sK3,sK2) & v7_waybel_0(sK3) & v4_orders_2(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f24,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK2,X1,u1_struct_0(sK2)) & l1_waybel_0(X1,sK2) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X1] : (~r1_waybel_0(sK2,X1,u1_struct_0(sK2)) & l1_waybel_0(X1,sK2) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) & l1_waybel_0(sK3,sK2) & v7_waybel_0(sK3) & v4_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) | ~spl9_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl9_8 <=> r1_waybel_0(sK2,sK3,u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl9_7 | spl9_8 | ~spl9_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f120,f129,f125])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl9_6 <=> ! [X0] : (r2_waybel_0(sK2,sK3,X0) | r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    r1_waybel_0(sK2,sK3,u1_struct_0(sK2)) | r2_waybel_0(sK2,sK3,k1_xboole_0) | ~spl9_6),
% 0.21/0.48    inference(superposition,[],[f121,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X0] : (r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0)) | r2_waybel_0(sK2,sK3,X0)) ) | ~spl9_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f120])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    spl9_3 | spl9_6 | ~spl9_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f118,f113,f120,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl9_3 <=> v2_struct_0(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl9_5 <=> ! [X1,X0] : (r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1)) | r2_waybel_0(sK2,X0,X1) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X0] : (r2_waybel_0(sK2,sK3,X0) | v2_struct_0(sK3) | r1_waybel_0(sK2,sK3,k4_xboole_0(u1_struct_0(sK2),X0))) ) | ~spl9_5),
% 0.21/0.48    inference(resolution,[],[f114,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    l1_waybel_0(sK3,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_waybel_0(X0,sK2) | r2_waybel_0(sK2,X0,X1) | v2_struct_0(X0) | r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1))) ) | ~spl9_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~spl9_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    $false | ~spl9_1),
% 0.21/0.48    inference(resolution,[],[f84,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~v2_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    v2_struct_0(sK2) | ~spl9_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl9_1 <=> v2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl9_1 | spl9_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f111,f113,f82])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_waybel_0(sK2,X0,k4_xboole_0(u1_struct_0(sK2),X1)) | ~l1_waybel_0(X0,sK2) | v2_struct_0(X0) | r2_waybel_0(sK2,X0,X1) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f70,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    l1_struct_0(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f53,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ~spl9_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    $false | ~spl9_3),
% 0.21/0.48    inference(resolution,[],[f93,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~v2_struct_0(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    v2_struct_0(sK3) | ~spl9_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl9_3 | spl9_4 | ~spl9_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f89,f86,f95,f91])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl9_2 <=> ! [X0] : (~l1_waybel_0(X0,sK2) | sP1(sK2,X0) | v2_struct_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    sP1(sK2,sK3) | v2_struct_0(sK3) | ~spl9_2),
% 0.21/0.48    inference(resolution,[],[f87,f48])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_waybel_0(X0,sK2) | sP1(sK2,X0) | v2_struct_0(X0)) ) | ~spl9_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl9_1 | spl9_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f86,f82])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_waybel_0(X0,sK2) | v2_struct_0(X0) | sP1(sK2,X0) | v2_struct_0(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f61,f44])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | sP1(X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(definition_folding,[],[f17,f21,f20])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (12059)------------------------------
% 0.21/0.48  % (12059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12059)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (12059)Memory used [KB]: 6268
% 0.21/0.48  % (12059)Time elapsed: 0.087 s
% 0.21/0.48  % (12059)------------------------------
% 0.21/0.48  % (12059)------------------------------
% 0.21/0.48  % (12046)Success in time 0.124 s
%------------------------------------------------------------------------------
