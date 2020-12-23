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
% DateTime   : Thu Dec  3 13:22:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 147 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  306 ( 801 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f105,f73])).

fof(f73,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f105,plain,(
    r2_hidden(k2_waybel_0(sK3,sK4,sK6(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),k1_xboole_0) ),
    inference(resolution,[],[f103,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
            | ~ r1_orders_2(X1,X3,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ( r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0)
          & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
          & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(k2_waybel_0(X2,X1,X5),X0)
          & r1_orders_2(X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0)
        & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
            | ~ r1_orders_2(X1,X3,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ? [X5] :
            ( r2_hidden(k2_waybel_0(X2,X1,X5),X0)
            & r1_orders_2(X1,X3,X5)
            & m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,X3,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            & r1_orders_2(X1,X3,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ? [X4] :
          ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f103,plain,(
    sP0(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4))) ),
    inference(resolution,[],[f101,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X2,X1,X0)
      | sP0(X0,X1,X2,sK7(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f55,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f4,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,u1_struct_0(X1))
      | sP0(X2,X1,X0,X4)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ sP0(X2,X1,X0,sK5(X0,X1,X2))
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X2,X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ sP0(X2,X1,X0,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X2,X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X2,X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( sP0(X2,X1,X0,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( sP0(X2,X1,X0,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f101,plain,(
    sP1(sK3,sK4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f100,f89])).

fof(f89,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    & l1_waybel_0(sK4,sK3)
    & v7_waybel_0(sK4)
    & v4_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f25,f24])).

fof(f24,plain,
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
          ( ~ r1_waybel_0(sK3,X1,u1_struct_0(sK3))
          & l1_waybel_0(X1,sK3)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK3,X1,u1_struct_0(sK3))
        & l1_waybel_0(X1,sK3)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
      & l1_waybel_0(sK4,sK3)
      & v7_waybel_0(sK4)
      & v4_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f88,plain,
    ( sP2(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f87,f44])).

fof(f44,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,
    ( sP2(sK4,sK3)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f86,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,
    ( sP2(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f62,f48])).

fof(f48,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | sP2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f22,f21,f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( r2_waybel_0(X0,X1,X2)
        <=> sP1(X0,X1,X2) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f100,plain,
    ( sP1(sK3,sK4,k1_xboole_0)
    | ~ sP2(sK4,sK3) ),
    inference(resolution,[],[f99,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X1,X0,X2)
      | sP1(X1,X0,X2)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_waybel_0(X1,X0,X2)
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | ~ r2_waybel_0(X1,X0,X2) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( r2_waybel_0(X0,X1,X2)
            | ~ sP1(X0,X1,X2) )
          & ( sP1(X0,X1,X2)
            | ~ r2_waybel_0(X0,X1,X2) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f99,plain,(
    r2_waybel_0(sK3,sK4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f98,f49])).

fof(f49,plain,(
    ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,
    ( r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    | r2_waybel_0(sK3,sK4,k1_xboole_0) ),
    inference(superposition,[],[f96,f77])).

fof(f77,plain,(
    ! [X1] : k6_subset_1(X1,k1_xboole_0) = X1 ),
    inference(resolution,[],[f72,f75])).

fof(f75,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f66,f73])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f18,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f96,plain,(
    ! [X0] :
      ( r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0))
      | r2_waybel_0(sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X0] :
      ( r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0))
      | r2_waybel_0(sK3,sK4,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f94,plain,(
    ! [X0] :
      ( r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0))
      | r2_waybel_0(sK3,sK4,X0)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f93,f45])).

fof(f93,plain,(
    ! [X0] :
      ( r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0))
      | r2_waybel_0(sK3,sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_struct_0(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f52,f48])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:37 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.45  % (28142)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (28137)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (28142)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f105,f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(resolution,[],[f70,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    r2_hidden(k2_waybel_0(sK3,sK4,sK6(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),k1_xboole_0)),
% 0.20/0.46    inference(resolution,[],[f103,f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)))) & ((r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0) & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ! [X3,X2,X1,X0] : (? [X5] : (r2_hidden(k2_waybel_0(X2,X1,X5),X0) & r1_orders_2(X1,X3,X5) & m1_subset_1(X5,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X2,X1,sK6(X0,X1,X2,X3)),X0) & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3)) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X5] : (r2_hidden(k2_waybel_0(X2,X1,X5),X0) & r1_orders_2(X1,X3,X5) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.46    inference(rectify,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X2,X1,X0,X3)))),
% 0.20/0.46    inference(nnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    sP0(k1_xboole_0,sK4,sK3,sK7(u1_struct_0(sK4)))),
% 0.20/0.46    inference(resolution,[],[f101,f90])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~sP1(X2,X1,X0) | sP0(X0,X1,X2,sK7(u1_struct_0(X1)))) )),
% 0.20/0.46    inference(resolution,[],[f55,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(sK7(X0),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ! [X0] : m1_subset_1(sK7(X0),X0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f4,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK7(X0),X0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X4,u1_struct_0(X1)) | sP0(X2,X1,X0,X4) | ~sP1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~sP0(X2,X1,X0,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (sP0(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ! [X2,X1,X0] : (? [X3] : (~sP0(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~sP0(X2,X1,X0,sK5(X0,X1,X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~sP0(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (sP0(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.20/0.46    inference(rectify,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~sP0(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (sP0(X2,X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.20/0.46    inference(nnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (sP0(X2,X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1))))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    sP1(sK3,sK4,k1_xboole_0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f100,f89])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    sP2(sK4,sK3)),
% 0.20/0.46    inference(subsumption_resolution,[],[f88,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ~v2_struct_0(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f13,f25,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    sP2(sK4,sK3) | v2_struct_0(sK3)),
% 0.20/0.46    inference(subsumption_resolution,[],[f87,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    l1_struct_0(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    sP2(sK4,sK3) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.46    inference(subsumption_resolution,[],[f86,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ~v2_struct_0(sK4)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    sP2(sK4,sK3) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.20/0.46    inference(resolution,[],[f62,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    l1_waybel_0(sK4,sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | sP2(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (sP2(X1,X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(definition_folding,[],[f17,f22,f21,f20])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X1,X0] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> sP1(X0,X1,X2)) | ~sP2(X1,X0))),
% 0.20/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    sP1(sK3,sK4,k1_xboole_0) | ~sP2(sK4,sK3)),
% 0.20/0.46    inference(resolution,[],[f99,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_waybel_0(X1,X0,X2) | sP1(X1,X0,X2) | ~sP2(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : ((r2_waybel_0(X1,X0,X2) | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | ~r2_waybel_0(X1,X0,X2))) | ~sP2(X0,X1))),
% 0.20/0.46    inference(rectify,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X1,X0] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | ~r2_waybel_0(X0,X1,X2))) | ~sP2(X1,X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f22])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    r2_waybel_0(sK3,sK4,k1_xboole_0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f98,f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ~r1_waybel_0(sK3,sK4,u1_struct_0(sK3))),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) | r2_waybel_0(sK3,sK4,k1_xboole_0)),
% 0.20/0.46    inference(superposition,[],[f96,f77])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X1] : (k6_subset_1(X1,k1_xboole_0) = X1) )),
% 0.20/0.46    inference(resolution,[],[f72,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(resolution,[],[f66,f73])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f18,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f68,f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ( ! [X0] : (r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) | r2_waybel_0(sK3,sK4,X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f95,f43])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ( ! [X0] : (r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) | r2_waybel_0(sK3,sK4,X0) | v2_struct_0(sK3)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f94,f44])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ( ! [X0] : (r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) | r2_waybel_0(sK3,sK4,X0) | ~l1_struct_0(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f93,f45])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ( ! [X0] : (r1_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),X0)) | r2_waybel_0(sK3,sK4,X0) | v2_struct_0(sK4) | ~l1_struct_0(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.46    inference(resolution,[],[f52,f48])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (28142)------------------------------
% 0.20/0.46  % (28142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (28142)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (28142)Memory used [KB]: 1663
% 0.20/0.46  % (28142)Time elapsed: 0.041 s
% 0.20/0.46  % (28142)------------------------------
% 0.20/0.46  % (28142)------------------------------
% 0.20/0.47  % (28129)Success in time 0.106 s
%------------------------------------------------------------------------------
