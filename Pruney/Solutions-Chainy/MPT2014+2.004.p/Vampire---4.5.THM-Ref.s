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
% DateTime   : Thu Dec  3 13:23:03 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 703 expanded)
%              Number of leaves         :   16 ( 248 expanded)
%              Depth                    :   29
%              Number of atoms          :  462 (4602 expanded)
%              Number of equality atoms :   47 ( 310 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f201,f84])).

fof(f84,plain,(
    l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f83,f41])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_waybel_0(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK1,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK1,X1,X2)),u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,X2)),u1_struct_0(sK2))
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & l1_waybel_0(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,X2)),u1_struct_0(sK2))
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f83,plain,
    ( l1_orders_2(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f49,f43])).

fof(f43,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f201,plain,(
    ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f200,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f200,plain,(
    ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f198,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f198,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2) ),
    inference(resolution,[],[f194,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_struct_0(X0)
          | ~ v1_xboole_0(u1_struct_0(X0)) )
        & ( v1_xboole_0(u1_struct_0(X0))
          | ~ v2_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
      <=> v1_xboole_0(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).

fof(f194,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f193,f45])).

fof(f45,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f193,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f188,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f188,plain,
    ( r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f181,f187])).

fof(f187,plain,(
    r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) ),
    inference(subsumption_resolution,[],[f184,f186])).

fof(f186,plain,(
    m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f185,f45])).

fof(f185,plain,
    ( m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)) ),
    inference(resolution,[],[f182,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f182,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))
    | m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f179,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f179,plain,
    ( m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[],[f105,f176])).

fof(f176,plain,(
    sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)) = sK6(sK3,sK2,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))) ),
    inference(resolution,[],[f111,f45])).

fof(f111,plain,(
    ! [X0] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0)
      | sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0) = sK6(sK3,sK2,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0)) ) ),
    inference(resolution,[],[f107,f66])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))
      | sK6(sK3,sK2,X0) = X0 ) ),
    inference(resolution,[],[f106,f44])).

fof(f106,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK2))
      | ~ r2_hidden(X7,u1_struct_0(k4_waybel_9(sK1,sK2,X6)))
      | sK6(X6,sK2,X7) = X7 ) ),
    inference(resolution,[],[f100,f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,u1_struct_0(X2))
      | sK6(X0,X1,X6) = X6 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_orders_2(X1,X0,X4)
                | sK4(X0,X1,X2) != X4
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(sK4(X0,X1,X2),u1_struct_0(X2)) )
          & ( ( r1_orders_2(X1,X0,sK5(X0,X1,X2))
              & sK4(X0,X1,X2) = sK5(X0,X1,X2)
              & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
            | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X2)) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,u1_struct_0(X2))
              | ! [X7] :
                  ( ~ r1_orders_2(X1,X0,X7)
                  | X6 != X7
                  | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
            & ( ( r1_orders_2(X1,X0,sK6(X0,X1,X6))
                & sK6(X0,X1,X6) = X6
                & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1)) )
              | ~ r2_hidden(X6,u1_struct_0(X2)) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_orders_2(X1,X0,X4)
                | X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ r2_hidden(X3,u1_struct_0(X2)) )
          & ( ? [X5] :
                ( r1_orders_2(X1,X0,X5)
                & X3 = X5
                & m1_subset_1(X5,u1_struct_0(X1)) )
            | r2_hidden(X3,u1_struct_0(X2)) ) )
     => ( ( ! [X4] :
              ( ~ r1_orders_2(X1,X0,X4)
              | sK4(X0,X1,X2) != X4
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(sK4(X0,X1,X2),u1_struct_0(X2)) )
        & ( ? [X5] :
              ( r1_orders_2(X1,X0,X5)
              & sK4(X0,X1,X2) = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X2)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_orders_2(X1,X0,X5)
          & sK4(X0,X1,X2) = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X0,sK5(X0,X1,X2))
        & sK4(X0,X1,X2) = sK5(X0,X1,X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_orders_2(X1,X0,X8)
          & X6 = X8
          & m1_subset_1(X8,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X0,sK6(X0,X1,X6))
        & sK6(X0,X1,X6) = X6
        & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_orders_2(X1,X0,X4)
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ r2_hidden(X3,u1_struct_0(X2)) )
            & ( ? [X5] :
                  ( r1_orders_2(X1,X0,X5)
                  & X3 = X5
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X3,u1_struct_0(X2)) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,u1_struct_0(X2))
              | ! [X7] :
                  ( ~ r1_orders_2(X1,X0,X7)
                  | X6 != X7
                  | ~ m1_subset_1(X7,u1_struct_0(X1)) ) )
            & ( ? [X8] :
                  ( r1_orders_2(X1,X0,X8)
                  & X6 = X8
                  & m1_subset_1(X8,u1_struct_0(X1)) )
              | ~ r2_hidden(X6,u1_struct_0(X2)) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X3] :
      ( ( sP0(X2,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_orders_2(X1,X2,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X3)) )
            & ( ? [X5] :
                  ( r1_orders_2(X1,X2,X5)
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X4,u1_struct_0(X3)) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,u1_struct_0(X3))
              | ! [X5] :
                  ( ~ r1_orders_2(X1,X2,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
            & ( ? [X5] :
                  ( r1_orders_2(X1,X2,X5)
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X3)) ) )
        | ~ sP0(X2,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X2,X1,X3] :
      ( sP0(X2,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,u1_struct_0(X3))
        <=> ? [X5] :
              ( r1_orders_2(X1,X2,X5)
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f100,plain,(
    ! [X0] :
      ( sP0(X0,sK2,k4_waybel_9(sK1,sK2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f98,f42])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2)
      | sP0(X0,sK2,k4_waybel_9(sK1,sK2,X0)) ) ),
    inference(resolution,[],[f97,f43])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | sP0(X0,X1,k4_waybel_9(sK1,X1,X0)) ) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,sK1)
      | v2_struct_0(X1)
      | sP0(X0,X1,k4_waybel_9(sK1,X1,X0))
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f78,f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | sP0(X2,X1,k4_waybel_9(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f75,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

% (12112)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,k4_waybel_9(X0,X1,X2))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f74,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,k4_waybel_9(X0,X1,X2))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X3)
      | k4_waybel_9(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ~ sP0(X2,X1,X3) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & sP0(X2,X1,X3) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

% (12109)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k4_waybel_9(X0,X1,X2) = X3
                      | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      | ~ sP0(X2,X1,X3) )
                    & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                        & sP0(X2,X1,X3) )
                      | k4_waybel_9(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & sP0(X2,X1,X3) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f22])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (12112)Refutation not found, incomplete strategy% (12112)------------------------------
% (12112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12112)Termination reason: Refutation not found, incomplete strategy

% (12112)Memory used [KB]: 10618
% (12112)Time elapsed: 0.098 s
% (12112)------------------------------
% (12112)------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f105,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK6(X4,sK2,X5),u1_struct_0(sK2))
      | ~ r2_hidden(X5,u1_struct_0(k4_waybel_9(sK1,sK2,X4)))
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f100,f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,u1_struct_0(X2))
      | m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f184,plain,
    ( ~ m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))
    | r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) ),
    inference(subsumption_resolution,[],[f183,f44])).

fof(f183,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))
    | r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) ),
    inference(resolution,[],[f180,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK2,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | r2_hidden(X1,u1_struct_0(k4_waybel_9(sK1,sK2,X0))) ) ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r1_orders_2(X1,X0,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | r2_hidden(X7,u1_struct_0(X2)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,u1_struct_0(X2))
      | ~ r1_orders_2(X1,X0,X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f180,plain,(
    r1_orders_2(sK2,sK3,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f177,f45])).

fof(f177,plain,
    ( r1_orders_2(sK2,sK3,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)) ),
    inference(superposition,[],[f119,f176])).

fof(f119,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,sK3,sK6(sK3,sK2,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0)))
      | r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0) ) ),
    inference(resolution,[],[f115,f66])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))
      | r1_orders_2(sK2,sK3,sK6(sK3,sK2,X0)) ) ),
    inference(resolution,[],[f104,f44])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ r2_hidden(X3,u1_struct_0(k4_waybel_9(sK1,sK2,X2)))
      | r1_orders_2(sK2,X2,sK6(X2,sK2,X3)) ) ),
    inference(resolution,[],[f100,f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,u1_struct_0(X2))
      | r1_orders_2(X1,X0,sK6(X0,X1,X6)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f181,plain,
    ( r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f178,f44])).

fof(f178,plain,
    ( r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(superposition,[],[f125,f176])).

fof(f125,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK6(X7,sK2,X6),u1_struct_0(sK2))
      | ~ m1_subset_1(X7,u1_struct_0(sK2))
      | ~ r2_hidden(X6,u1_struct_0(k4_waybel_9(sK1,sK2,X7)))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f105,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.38  ipcrm: permission denied for id (797114369)
% 0.14/0.38  ipcrm: permission denied for id (797212674)
% 0.14/0.38  ipcrm: permission denied for id (804913155)
% 0.14/0.38  ipcrm: permission denied for id (801472516)
% 0.14/0.38  ipcrm: permission denied for id (797310981)
% 0.14/0.38  ipcrm: permission denied for id (803766278)
% 0.14/0.39  ipcrm: permission denied for id (801538055)
% 0.14/0.39  ipcrm: permission denied for id (797409288)
% 0.14/0.39  ipcrm: permission denied for id (804945929)
% 0.14/0.39  ipcrm: permission denied for id (797474826)
% 0.14/0.39  ipcrm: permission denied for id (797540364)
% 0.14/0.40  ipcrm: permission denied for id (797573133)
% 0.14/0.40  ipcrm: permission denied for id (797605902)
% 0.14/0.40  ipcrm: permission denied for id (803897360)
% 0.14/0.40  ipcrm: permission denied for id (797704209)
% 0.14/0.40  ipcrm: permission denied for id (797736978)
% 0.14/0.41  ipcrm: permission denied for id (805044243)
% 0.14/0.41  ipcrm: permission denied for id (801767445)
% 0.14/0.41  ipcrm: permission denied for id (801800214)
% 0.22/0.41  ipcrm: permission denied for id (801832983)
% 0.22/0.41  ipcrm: permission denied for id (797933592)
% 0.22/0.41  ipcrm: permission denied for id (801865753)
% 0.22/0.42  ipcrm: permission denied for id (801898522)
% 0.22/0.42  ipcrm: permission denied for id (798064667)
% 0.22/0.42  ipcrm: permission denied for id (801931292)
% 0.22/0.42  ipcrm: permission denied for id (798162974)
% 0.22/0.42  ipcrm: permission denied for id (798195743)
% 0.22/0.43  ipcrm: permission denied for id (804028448)
% 0.22/0.43  ipcrm: permission denied for id (802029601)
% 0.22/0.43  ipcrm: permission denied for id (798294050)
% 0.22/0.43  ipcrm: permission denied for id (798359588)
% 0.22/0.43  ipcrm: permission denied for id (798392357)
% 0.22/0.43  ipcrm: permission denied for id (802095142)
% 0.22/0.43  ipcrm: permission denied for id (802127911)
% 0.22/0.44  ipcrm: permission denied for id (804093992)
% 0.22/0.44  ipcrm: permission denied for id (798523433)
% 0.22/0.44  ipcrm: permission denied for id (804126762)
% 0.22/0.44  ipcrm: permission denied for id (802226219)
% 0.22/0.44  ipcrm: permission denied for id (798621740)
% 0.22/0.44  ipcrm: permission denied for id (798654509)
% 0.22/0.44  ipcrm: permission denied for id (802258990)
% 0.22/0.44  ipcrm: permission denied for id (798720047)
% 0.22/0.45  ipcrm: permission denied for id (802291760)
% 0.22/0.45  ipcrm: permission denied for id (798785585)
% 0.22/0.45  ipcrm: permission denied for id (798818354)
% 0.22/0.45  ipcrm: permission denied for id (798851123)
% 0.22/0.45  ipcrm: permission denied for id (798883892)
% 0.22/0.45  ipcrm: permission denied for id (802324533)
% 0.22/0.45  ipcrm: permission denied for id (798949430)
% 0.22/0.46  ipcrm: permission denied for id (802357303)
% 0.22/0.46  ipcrm: permission denied for id (799014968)
% 0.22/0.46  ipcrm: permission denied for id (802390073)
% 0.22/0.46  ipcrm: permission denied for id (799080506)
% 0.22/0.46  ipcrm: permission denied for id (799113275)
% 0.22/0.46  ipcrm: permission denied for id (799146044)
% 0.22/0.47  ipcrm: permission denied for id (804159549)
% 0.22/0.47  ipcrm: permission denied for id (802455614)
% 0.22/0.47  ipcrm: permission denied for id (799244351)
% 0.22/0.47  ipcrm: permission denied for id (802488384)
% 0.22/0.47  ipcrm: permission denied for id (799309889)
% 0.22/0.47  ipcrm: permission denied for id (799342658)
% 0.22/0.47  ipcrm: permission denied for id (799375427)
% 0.22/0.48  ipcrm: permission denied for id (799408196)
% 0.22/0.48  ipcrm: permission denied for id (802521157)
% 0.22/0.48  ipcrm: permission denied for id (802553926)
% 0.22/0.48  ipcrm: permission denied for id (802586695)
% 0.22/0.48  ipcrm: permission denied for id (804192328)
% 0.22/0.48  ipcrm: permission denied for id (804225097)
% 0.22/0.48  ipcrm: permission denied for id (805175370)
% 0.22/0.49  ipcrm: permission denied for id (804290635)
% 0.22/0.49  ipcrm: permission denied for id (799670348)
% 0.22/0.49  ipcrm: permission denied for id (799703117)
% 0.22/0.49  ipcrm: permission denied for id (804323406)
% 0.22/0.49  ipcrm: permission denied for id (799768655)
% 0.22/0.49  ipcrm: permission denied for id (799801424)
% 0.22/0.49  ipcrm: permission denied for id (799834193)
% 0.22/0.49  ipcrm: permission denied for id (804356178)
% 0.22/0.49  ipcrm: permission denied for id (805208147)
% 0.22/0.49  ipcrm: permission denied for id (804421716)
% 0.22/0.49  ipcrm: permission denied for id (799998038)
% 0.22/0.49  ipcrm: permission denied for id (800063576)
% 0.22/0.49  ipcrm: permission denied for id (802947161)
% 0.22/0.50  ipcrm: permission denied for id (802979930)
% 0.22/0.50  ipcrm: permission denied for id (803012699)
% 0.22/0.50  ipcrm: permission denied for id (800227421)
% 0.22/0.50  ipcrm: permission denied for id (800260190)
% 0.22/0.50  ipcrm: permission denied for id (800292959)
% 0.22/0.50  ipcrm: permission denied for id (803143776)
% 0.22/0.50  ipcrm: permission denied for id (800358497)
% 0.22/0.50  ipcrm: permission denied for id (804552802)
% 0.22/0.50  ipcrm: permission denied for id (803176547)
% 0.22/0.50  ipcrm: permission denied for id (800456804)
% 0.22/0.51  ipcrm: permission denied for id (803209317)
% 0.22/0.51  ipcrm: permission denied for id (800555111)
% 0.22/0.51  ipcrm: permission denied for id (804618344)
% 0.22/0.51  ipcrm: permission denied for id (800620649)
% 0.22/0.51  ipcrm: permission denied for id (804651114)
% 0.22/0.51  ipcrm: permission denied for id (803340395)
% 0.22/0.51  ipcrm: permission denied for id (803373164)
% 0.22/0.51  ipcrm: permission denied for id (800751725)
% 0.22/0.51  ipcrm: permission denied for id (800784494)
% 0.22/0.51  ipcrm: permission denied for id (805372015)
% 0.22/0.51  ipcrm: permission denied for id (800850032)
% 0.22/0.51  ipcrm: permission denied for id (800882801)
% 0.22/0.51  ipcrm: permission denied for id (800915570)
% 0.22/0.52  ipcrm: permission denied for id (803438707)
% 0.22/0.52  ipcrm: permission denied for id (805437556)
% 0.22/0.52  ipcrm: permission denied for id (801046645)
% 0.22/0.52  ipcrm: permission denied for id (801079414)
% 0.22/0.52  ipcrm: permission denied for id (801144952)
% 0.22/0.52  ipcrm: permission denied for id (804782201)
% 0.22/0.52  ipcrm: permission denied for id (804814970)
% 0.22/0.52  ipcrm: permission denied for id (803602555)
% 0.22/0.52  ipcrm: permission denied for id (803635324)
% 0.22/0.52  ipcrm: permission denied for id (801308797)
% 0.22/0.52  ipcrm: permission denied for id (804847742)
% 0.22/0.52  ipcrm: permission denied for id (801374335)
% 0.98/0.63  % (12126)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.98/0.63  % (12118)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.98/0.64  % (12110)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.67  % (12110)Refutation found. Thanks to Tanya!
% 1.28/0.67  % SZS status Theorem for theBenchmark
% 1.28/0.67  % SZS output start Proof for theBenchmark
% 1.28/0.67  fof(f202,plain,(
% 1.28/0.67    $false),
% 1.28/0.67    inference(subsumption_resolution,[],[f201,f84])).
% 1.28/0.67  fof(f84,plain,(
% 1.28/0.67    l1_orders_2(sK2)),
% 1.28/0.67    inference(subsumption_resolution,[],[f83,f41])).
% 1.28/0.67  fof(f41,plain,(
% 1.28/0.67    l1_struct_0(sK1)),
% 1.28/0.67    inference(cnf_transformation,[],[f27])).
% 1.28/0.67  fof(f27,plain,(
% 1.28/0.67    ((~r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_waybel_0(sK2,sK1) & ~v2_struct_0(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)),
% 1.28/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f26,f25,f24])).
% 1.28/0.67  fof(f24,plain,(
% 1.28/0.67    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK1,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK1) & ~v2_struct_0(X1)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f25,plain,(
% 1.28/0.67    ? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK1,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK1) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,X2)),u1_struct_0(sK2)) & m1_subset_1(X2,u1_struct_0(sK2))) & l1_waybel_0(sK2,sK1) & ~v2_struct_0(sK2))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f26,plain,(
% 1.28/0.67    ? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,X2)),u1_struct_0(sK2)) & m1_subset_1(X2,u1_struct_0(sK2))) => (~r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f12,plain,(
% 1.28/0.67    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.28/0.67    inference(flattening,[],[f11])).
% 1.28/0.67  fof(f11,plain,(
% 1.28/0.67    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f9])).
% 1.28/0.67  fof(f9,negated_conjecture,(
% 1.28/0.67    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 1.28/0.67    inference(negated_conjecture,[],[f8])).
% 1.28/0.67  fof(f8,conjecture,(
% 1.28/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 1.28/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).
% 1.28/0.67  fof(f83,plain,(
% 1.28/0.67    l1_orders_2(sK2) | ~l1_struct_0(sK1)),
% 1.28/0.67    inference(resolution,[],[f49,f43])).
% 1.28/0.67  fof(f43,plain,(
% 1.28/0.67    l1_waybel_0(sK2,sK1)),
% 1.28/0.67    inference(cnf_transformation,[],[f27])).
% 1.28/0.67  fof(f49,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | l1_orders_2(X1) | ~l1_struct_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f15])).
% 1.28/0.67  fof(f15,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.28/0.67    inference(ennf_transformation,[],[f4])).
% 1.28/0.67  fof(f4,axiom,(
% 1.28/0.67    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.28/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 1.28/0.67  fof(f201,plain,(
% 1.28/0.67    ~l1_orders_2(sK2)),
% 1.28/0.67    inference(resolution,[],[f200,f46])).
% 1.28/0.67  fof(f46,plain,(
% 1.28/0.67    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f13])).
% 1.28/0.67  fof(f13,plain,(
% 1.28/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.28/0.67    inference(ennf_transformation,[],[f3])).
% 1.28/0.67  fof(f3,axiom,(
% 1.28/0.67    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.28/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.28/0.67  fof(f200,plain,(
% 1.28/0.67    ~l1_struct_0(sK2)),
% 1.28/0.67    inference(subsumption_resolution,[],[f198,f42])).
% 1.28/0.67  fof(f42,plain,(
% 1.28/0.67    ~v2_struct_0(sK2)),
% 1.28/0.67    inference(cnf_transformation,[],[f27])).
% 1.28/0.67  fof(f198,plain,(
% 1.28/0.67    v2_struct_0(sK2) | ~l1_struct_0(sK2)),
% 1.28/0.67    inference(resolution,[],[f194,f48])).
% 1.28/0.67  fof(f48,plain,(
% 1.28/0.67    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f28])).
% 1.28/0.67  fof(f28,plain,(
% 1.28/0.67    ! [X0] : (((v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) & (v1_xboole_0(u1_struct_0(X0)) | ~v2_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.28/0.67    inference(nnf_transformation,[],[f14])).
% 1.28/0.67  fof(f14,plain,(
% 1.28/0.67    ! [X0] : ((v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.28/0.67    inference(ennf_transformation,[],[f5])).
% 1.28/0.67  fof(f5,axiom,(
% 1.28/0.67    ! [X0] : (l1_struct_0(X0) => (v2_struct_0(X0) <=> v1_xboole_0(u1_struct_0(X0))))),
% 1.28/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_struct_0)).
% 1.28/0.67  fof(f194,plain,(
% 1.28/0.67    v1_xboole_0(u1_struct_0(sK2))),
% 1.28/0.67    inference(subsumption_resolution,[],[f193,f45])).
% 1.28/0.67  fof(f45,plain,(
% 1.28/0.67    ~r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))),
% 1.28/0.67    inference(cnf_transformation,[],[f27])).
% 1.28/0.67  fof(f193,plain,(
% 1.28/0.67    v1_xboole_0(u1_struct_0(sK2)) | r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))),
% 1.28/0.67    inference(resolution,[],[f188,f67])).
% 1.28/0.67  fof(f67,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f39])).
% 1.28/0.67  fof(f39,plain,(
% 1.28/0.67    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.28/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f38])).
% 1.28/0.67  fof(f38,plain,(
% 1.28/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f19,plain,(
% 1.28/0.67    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f10])).
% 1.28/0.67  fof(f10,plain,(
% 1.28/0.67    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.28/0.67    inference(unused_predicate_definition_removal,[],[f1])).
% 1.28/0.67  fof(f1,axiom,(
% 1.28/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.67  fof(f188,plain,(
% 1.28/0.67    r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 1.28/0.67    inference(subsumption_resolution,[],[f181,f187])).
% 1.28/0.67  fof(f187,plain,(
% 1.28/0.67    r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))),
% 1.28/0.67    inference(subsumption_resolution,[],[f184,f186])).
% 1.28/0.67  fof(f186,plain,(
% 1.28/0.67    m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))),
% 1.28/0.67    inference(subsumption_resolution,[],[f185,f45])).
% 1.28/0.67  fof(f185,plain,(
% 1.28/0.67    m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) | r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))),
% 1.28/0.67    inference(resolution,[],[f182,f66])).
% 1.28/0.67  fof(f66,plain,(
% 1.28/0.67    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f39])).
% 1.28/0.67  fof(f182,plain,(
% 1.28/0.67    ~r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) | m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2))),
% 1.28/0.67    inference(subsumption_resolution,[],[f179,f44])).
% 1.28/0.67  fof(f44,plain,(
% 1.28/0.67    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.28/0.67    inference(cnf_transformation,[],[f27])).
% 1.28/0.67  fof(f179,plain,(
% 1.28/0.67    m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) | ~r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) | ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.28/0.67    inference(superposition,[],[f105,f176])).
% 1.28/0.67  fof(f176,plain,(
% 1.28/0.67    sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)) = sK6(sK3,sK2,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)))),
% 1.28/0.67    inference(resolution,[],[f111,f45])).
% 1.28/0.67  fof(f111,plain,(
% 1.28/0.67    ( ! [X0] : (r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0) | sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0) = sK6(sK3,sK2,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0))) )),
% 1.28/0.67    inference(resolution,[],[f107,f66])).
% 1.28/0.67  fof(f107,plain,(
% 1.28/0.67    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) | sK6(sK3,sK2,X0) = X0) )),
% 1.28/0.67    inference(resolution,[],[f106,f44])).
% 1.28/0.67  fof(f106,plain,(
% 1.28/0.67    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK2)) | ~r2_hidden(X7,u1_struct_0(k4_waybel_9(sK1,sK2,X6))) | sK6(X6,sK2,X7) = X7) )),
% 1.28/0.67    inference(resolution,[],[f100,f51])).
% 1.28/0.67  fof(f51,plain,(
% 1.28/0.67    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,u1_struct_0(X2)) | sK6(X0,X1,X6) = X6) )),
% 1.28/0.67    inference(cnf_transformation,[],[f34])).
% 1.28/0.67  fof(f34,plain,(
% 1.28/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_orders_2(X1,X0,X4) | sK4(X0,X1,X2) != X4 | ~m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(sK4(X0,X1,X2),u1_struct_0(X2))) & ((r1_orders_2(X1,X0,sK5(X0,X1,X2)) & sK4(X0,X1,X2) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))) | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X2))))) & (! [X6] : ((r2_hidden(X6,u1_struct_0(X2)) | ! [X7] : (~r1_orders_2(X1,X0,X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X1)))) & ((r1_orders_2(X1,X0,sK6(X0,X1,X6)) & sK6(X0,X1,X6) = X6 & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1))) | ~r2_hidden(X6,u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.28/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).
% 1.28/0.67  fof(f31,plain,(
% 1.28/0.67    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_orders_2(X1,X0,X4) | X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X3,u1_struct_0(X2))) & (? [X5] : (r1_orders_2(X1,X0,X5) & X3 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X3,u1_struct_0(X2)))) => ((! [X4] : (~r1_orders_2(X1,X0,X4) | sK4(X0,X1,X2) != X4 | ~m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(sK4(X0,X1,X2),u1_struct_0(X2))) & (? [X5] : (r1_orders_2(X1,X0,X5) & sK4(X0,X1,X2) = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(sK4(X0,X1,X2),u1_struct_0(X2)))))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f32,plain,(
% 1.28/0.67    ! [X2,X1,X0] : (? [X5] : (r1_orders_2(X1,X0,X5) & sK4(X0,X1,X2) = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (r1_orders_2(X1,X0,sK5(X0,X1,X2)) & sK4(X0,X1,X2) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f33,plain,(
% 1.28/0.67    ! [X6,X1,X0] : (? [X8] : (r1_orders_2(X1,X0,X8) & X6 = X8 & m1_subset_1(X8,u1_struct_0(X1))) => (r1_orders_2(X1,X0,sK6(X0,X1,X6)) & sK6(X0,X1,X6) = X6 & m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1))))),
% 1.28/0.67    introduced(choice_axiom,[])).
% 1.28/0.67  fof(f30,plain,(
% 1.28/0.67    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_orders_2(X1,X0,X4) | X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X3,u1_struct_0(X2))) & (? [X5] : (r1_orders_2(X1,X0,X5) & X3 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X3,u1_struct_0(X2))))) & (! [X6] : ((r2_hidden(X6,u1_struct_0(X2)) | ! [X7] : (~r1_orders_2(X1,X0,X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X1)))) & (? [X8] : (r1_orders_2(X1,X0,X8) & X6 = X8 & m1_subset_1(X8,u1_struct_0(X1))) | ~r2_hidden(X6,u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.28/0.67    inference(rectify,[],[f29])).
% 1.28/0.67  fof(f29,plain,(
% 1.28/0.67    ! [X2,X1,X3] : ((sP0(X2,X1,X3) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3))))) & (! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3)))) | ~sP0(X2,X1,X3)))),
% 1.28/0.67    inference(nnf_transformation,[],[f22])).
% 1.28/0.67  fof(f22,plain,(
% 1.28/0.67    ! [X2,X1,X3] : (sP0(X2,X1,X3) <=> ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))),
% 1.28/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.28/0.67  fof(f100,plain,(
% 1.28/0.67    ( ! [X0] : (sP0(X0,sK2,k4_waybel_9(sK1,sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f98,f42])).
% 1.28/0.67  fof(f98,plain,(
% 1.28/0.67    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(sK2) | sP0(X0,sK2,k4_waybel_9(sK1,sK2,X0))) )),
% 1.28/0.67    inference(resolution,[],[f97,f43])).
% 1.28/0.67  fof(f97,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~l1_waybel_0(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | sP0(X0,X1,k4_waybel_9(sK1,X1,X0))) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f95,f40])).
% 1.28/0.67  fof(f40,plain,(
% 1.28/0.67    ~v2_struct_0(sK1)),
% 1.28/0.67    inference(cnf_transformation,[],[f27])).
% 1.28/0.67  fof(f95,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X1,sK1) | v2_struct_0(X1) | sP0(X0,X1,k4_waybel_9(sK1,X1,X0)) | v2_struct_0(sK1)) )),
% 1.28/0.67    inference(resolution,[],[f78,f41])).
% 1.28/0.67  fof(f78,plain,(
% 1.28/0.67    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | sP0(X2,X1,k4_waybel_9(X0,X1,X2)) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f75,f68])).
% 1.28/0.67  fof(f68,plain,(
% 1.28/0.67    ( ! [X2,X0,X1] : (v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f21])).
% 1.28/0.67  fof(f21,plain,(
% 1.28/0.67    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.28/0.67    inference(flattening,[],[f20])).
% 1.28/0.67  fof(f20,plain,(
% 1.28/0.67    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f7])).
% 1.28/0.67  fof(f7,axiom,(
% 1.28/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 1.28/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).
% 1.28/0.67  % (12112)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.67  fof(f75,plain,(
% 1.28/0.67    ( ! [X2,X0,X1] : (sP0(X2,X1,k4_waybel_9(X0,X1,X2)) | ~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(subsumption_resolution,[],[f74,f69])).
% 1.28/0.67  fof(f69,plain,(
% 1.28/0.67    ( ! [X2,X0,X1] : (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f21])).
% 1.28/0.67  fof(f74,plain,(
% 1.28/0.67    ( ! [X2,X0,X1] : (sP0(X2,X1,k4_waybel_9(X0,X1,X2)) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(equality_resolution,[],[f58])).
% 1.28/0.67  fof(f58,plain,(
% 1.28/0.67    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X3) | k4_waybel_9(X0,X1,X2) != X3 | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f36])).
% 1.28/0.67  fof(f36,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_waybel_9(X0,X1,X2) = X3 | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ~sP0(X2,X1,X3)) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & sP0(X2,X1,X3)) | k4_waybel_9(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.28/0.67    inference(flattening,[],[f35])).
% 1.28/0.67  % (12109)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.67  fof(f35,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k4_waybel_9(X0,X1,X2) = X3 | (u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ~sP0(X2,X1,X3))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & sP0(X2,X1,X3)) | k4_waybel_9(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.28/0.67    inference(nnf_transformation,[],[f23])).
% 1.28/0.67  fof(f23,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & sP0(X2,X1,X3))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.28/0.67    inference(definition_folding,[],[f17,f22])).
% 1.28/0.67  fof(f17,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.28/0.67    inference(flattening,[],[f16])).
% 1.28/0.67  fof(f16,plain,(
% 1.28/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f6])).
% 1.28/0.67  % (12112)Refutation not found, incomplete strategy% (12112)------------------------------
% 1.28/0.67  % (12112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.67  % (12112)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.67  
% 1.28/0.67  % (12112)Memory used [KB]: 10618
% 1.28/0.67  % (12112)Time elapsed: 0.098 s
% 1.28/0.67  % (12112)------------------------------
% 1.28/0.67  % (12112)------------------------------
% 1.28/0.67  fof(f6,axiom,(
% 1.28/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 1.28/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).
% 1.28/0.67  fof(f105,plain,(
% 1.28/0.67    ( ! [X4,X5] : (m1_subset_1(sK6(X4,sK2,X5),u1_struct_0(sK2)) | ~r2_hidden(X5,u1_struct_0(k4_waybel_9(sK1,sK2,X4))) | ~m1_subset_1(X4,u1_struct_0(sK2))) )),
% 1.28/0.67    inference(resolution,[],[f100,f50])).
% 1.28/0.67  fof(f50,plain,(
% 1.28/0.67    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,u1_struct_0(X2)) | m1_subset_1(sK6(X0,X1,X6),u1_struct_0(X1))) )),
% 1.28/0.67    inference(cnf_transformation,[],[f34])).
% 1.28/0.67  fof(f184,plain,(
% 1.28/0.67    ~m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) | r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))),
% 1.28/0.67    inference(subsumption_resolution,[],[f183,f44])).
% 1.28/0.67  fof(f183,plain,(
% 1.28/0.67    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) | r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3)))),
% 1.28/0.67    inference(resolution,[],[f180,f103])).
% 1.28/0.67  fof(f103,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~r1_orders_2(sK2,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_hidden(X1,u1_struct_0(k4_waybel_9(sK1,sK2,X0)))) )),
% 1.28/0.67    inference(resolution,[],[f100,f71])).
% 1.28/0.67  fof(f71,plain,(
% 1.28/0.67    ( ! [X2,X0,X7,X1] : (~sP0(X0,X1,X2) | ~r1_orders_2(X1,X0,X7) | ~m1_subset_1(X7,u1_struct_0(X1)) | r2_hidden(X7,u1_struct_0(X2))) )),
% 1.28/0.67    inference(equality_resolution,[],[f53])).
% 1.28/0.67  fof(f53,plain,(
% 1.28/0.67    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,u1_struct_0(X2)) | ~r1_orders_2(X1,X0,X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X1)) | ~sP0(X0,X1,X2)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f34])).
% 1.28/0.67  fof(f180,plain,(
% 1.28/0.67    r1_orders_2(sK2,sK3,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)))),
% 1.28/0.67    inference(subsumption_resolution,[],[f177,f45])).
% 1.28/0.67  fof(f177,plain,(
% 1.28/0.67    r1_orders_2(sK2,sK3,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))) | r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2))),
% 1.28/0.67    inference(superposition,[],[f119,f176])).
% 1.28/0.67  fof(f119,plain,(
% 1.28/0.67    ( ! [X0] : (r1_orders_2(sK2,sK3,sK6(sK3,sK2,sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0))) | r1_tarski(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),X0)) )),
% 1.28/0.67    inference(resolution,[],[f115,f66])).
% 1.28/0.67  fof(f115,plain,(
% 1.28/0.67    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) | r1_orders_2(sK2,sK3,sK6(sK3,sK2,X0))) )),
% 1.28/0.67    inference(resolution,[],[f104,f44])).
% 1.28/0.67  fof(f104,plain,(
% 1.28/0.67    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK2)) | ~r2_hidden(X3,u1_struct_0(k4_waybel_9(sK1,sK2,X2))) | r1_orders_2(sK2,X2,sK6(X2,sK2,X3))) )),
% 1.28/0.67    inference(resolution,[],[f100,f52])).
% 1.28/0.67  fof(f52,plain,(
% 1.28/0.67    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,u1_struct_0(X2)) | r1_orders_2(X1,X0,sK6(X0,X1,X6))) )),
% 1.28/0.67    inference(cnf_transformation,[],[f34])).
% 1.28/0.67  fof(f181,plain,(
% 1.28/0.67    r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) | ~r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) | v1_xboole_0(u1_struct_0(sK2))),
% 1.28/0.67    inference(subsumption_resolution,[],[f178,f44])).
% 1.28/0.67  fof(f178,plain,(
% 1.28/0.67    r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~r2_hidden(sK7(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK2)),u1_struct_0(k4_waybel_9(sK1,sK2,sK3))) | v1_xboole_0(u1_struct_0(sK2))),
% 1.28/0.67    inference(superposition,[],[f125,f176])).
% 1.28/0.67  fof(f125,plain,(
% 1.28/0.67    ( ! [X6,X7] : (r2_hidden(sK6(X7,sK2,X6),u1_struct_0(sK2)) | ~m1_subset_1(X7,u1_struct_0(sK2)) | ~r2_hidden(X6,u1_struct_0(k4_waybel_9(sK1,sK2,X7))) | v1_xboole_0(u1_struct_0(sK2))) )),
% 1.28/0.67    inference(resolution,[],[f105,f62])).
% 1.28/0.67  fof(f62,plain,(
% 1.28/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.28/0.67    inference(cnf_transformation,[],[f37])).
% 1.28/0.67  fof(f37,plain,(
% 1.28/0.67    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.28/0.67    inference(nnf_transformation,[],[f18])).
% 1.28/0.67  fof(f18,plain,(
% 1.28/0.67    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.28/0.67    inference(ennf_transformation,[],[f2])).
% 1.28/0.67  fof(f2,axiom,(
% 1.28/0.67    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.28/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.28/0.67  % SZS output end Proof for theBenchmark
% 1.28/0.67  % (12110)------------------------------
% 1.28/0.67  % (12110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.67  % (12110)Termination reason: Refutation
% 1.28/0.67  
% 1.28/0.67  % (12110)Memory used [KB]: 6524
% 1.28/0.68  % (12110)Time elapsed: 0.078 s
% 1.28/0.68  % (12110)------------------------------
% 1.28/0.68  % (12110)------------------------------
% 1.28/0.68  % (12120)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.68  % (11960)Success in time 0.312 s
%------------------------------------------------------------------------------
