%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:13 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 241 expanded)
%              Number of clauses        :   50 (  56 expanded)
%              Number of leaves         :   14 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  473 (1325 expanded)
%              Number of equality atoms :   43 (  89 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(rectify,[],[f2])).

fof(f14,plain,(
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

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK7,u1_struct_0(X0))
        & l1_waybel_0(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK6,X1,u1_struct_0(sK6))
          & l1_waybel_0(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r1_waybel_0(sK6,sK7,u1_struct_0(sK6))
    & l1_waybel_0(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_struct_0(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f21,f41,f40])).

fof(f69,plain,(
    ~ r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
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
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f37,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5))
        & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5))
                      & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f35,f37,f36])).

fof(f60,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f32])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1625,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6),X0,u1_struct_0(sK6)),u1_struct_0(sK6))
    | k6_subset_1(u1_struct_0(sK6),X0) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6648,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),u1_struct_0(sK6))
    | k6_subset_1(u1_struct_0(sK6),k6_subset_1(X0,X1)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_6650,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),u1_struct_0(sK6))
    | k6_subset_1(u1_struct_0(sK6),k6_subset_1(sK6,sK6)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_6648])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3395,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(k2_waybel_0(X2,sK7,sK5(X2,sK7,X1,sK3(u1_struct_0(sK7)))),X1)
    | ~ r2_hidden(k2_waybel_0(X2,sK7,sK5(X2,sK7,X1,sK3(u1_struct_0(sK7)))),X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5975,plain,
    ( ~ r1_xboole_0(X0,k6_subset_1(X1,X2))
    | ~ r2_hidden(k2_waybel_0(X3,sK7,sK5(X3,sK7,k6_subset_1(X1,X2),sK3(u1_struct_0(sK7)))),X0)
    | ~ r2_hidden(k2_waybel_0(X3,sK7,sK5(X3,sK7,k6_subset_1(X1,X2),sK3(u1_struct_0(sK7)))),k6_subset_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3395])).

cnf(c_5977,plain,
    ( ~ r1_xboole_0(sK6,k6_subset_1(sK6,sK6))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),k6_subset_1(sK6,sK6))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),sK6) ),
    inference(instantiation,[status(thm)],[c_5975])).

cnf(c_1895,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK0(u1_struct_0(sK6),X1,u1_struct_0(sK6)),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK6),X1,u1_struct_0(sK6)),X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5360,plain,
    ( ~ r1_xboole_0(X0,k6_subset_1(X1,X2))
    | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X1,X2),u1_struct_0(sK6)),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X1,X2),u1_struct_0(sK6)),k6_subset_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_5365,plain,
    ( ~ r1_xboole_0(sK6,k6_subset_1(sK6,sK6))
    | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),k6_subset_1(sK6,sK6))
    | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_5360])).

cnf(c_19,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,negated_conjecture,
    ( ~ r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_472,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k6_subset_1(u1_struct_0(X0),X2) != u1_struct_0(sK6)
    | sK7 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_473,plain,
    ( r2_waybel_0(sK6,sK7,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | k6_subset_1(u1_struct_0(sK6),X0) != u1_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_477,plain,
    ( r2_waybel_0(sK6,sK7,X0)
    | k6_subset_1(u1_struct_0(sK6),X0) != u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_25,c_24,c_23,c_22])).

cnf(c_4249,plain,
    ( r2_waybel_0(sK6,sK7,k6_subset_1(X0,X1))
    | k6_subset_1(u1_struct_0(sK6),k6_subset_1(X0,X1)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_4256,plain,
    ( r2_waybel_0(sK6,sK7,k6_subset_1(sK6,sK6))
    | k6_subset_1(u1_struct_0(sK6),k6_subset_1(sK6,sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_4249])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3388,plain,
    ( r2_hidden(k2_waybel_0(X0,sK7,sK5(X0,sK7,k6_subset_1(X1,X2),sK3(u1_struct_0(sK7)))),X1)
    | ~ r2_hidden(k2_waybel_0(X0,sK7,sK5(X0,sK7,k6_subset_1(X1,X2),sK3(u1_struct_0(sK7)))),k6_subset_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3392,plain,
    ( ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),k6_subset_1(sK6,sK6))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),sK6) ),
    inference(instantiation,[status(thm)],[c_3388])).

cnf(c_16,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1591,plain,
    ( ~ r2_waybel_0(sK6,sK7,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,X1)),X0)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2107,plain,
    ( ~ r2_waybel_0(sK6,sK7,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK3(X1),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(X1))),X0)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1591])).

cnf(c_2241,plain,
    ( ~ r2_waybel_0(sK6,sK7,k6_subset_1(X0,X1))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK3(X2),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(X0,X1),sK3(X2))),k6_subset_1(X0,X1))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_3326,plain,
    ( ~ r2_waybel_0(sK6,sK7,k6_subset_1(X0,X1))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(X0,X1),sK3(u1_struct_0(sK7)))),k6_subset_1(X0,X1))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_3328,plain,
    ( ~ r2_waybel_0(sK6,sK7,k6_subset_1(sK6,sK6))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),k6_subset_1(sK6,sK6))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3326])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1371,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1372,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1375,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1979,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X2)) = iProver_top
    | r2_hidden(sK1(X0,k6_subset_1(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_1375])).

cnf(c_2092,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_1979])).

cnf(c_2093,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2092])).

cnf(c_2095,plain,
    ( r1_xboole_0(sK6,k6_subset_1(sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_1886,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1892,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),k6_subset_1(sK6,sK6))
    | r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),sK6) ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1630,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6),X0,u1_struct_0(sK6)),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK6),X0,u1_struct_0(sK6)),u1_struct_0(sK6))
    | k6_subset_1(u1_struct_0(sK6),X0) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1885,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),k6_subset_1(X0,X1))
    | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),u1_struct_0(sK6))
    | k6_subset_1(u1_struct_0(sK6),k6_subset_1(X0,X1)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_1888,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),k6_subset_1(sK6,sK6))
    | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),u1_struct_0(sK6))
    | k6_subset_1(u1_struct_0(sK6),k6_subset_1(sK6,sK6)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_13,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1666,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6650,c_5977,c_5365,c_4256,c_3392,c_3328,c_2095,c_1892,c_1888,c_1666,c_22,c_23,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n015.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 12:59:23 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 2.87/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.03  
% 2.87/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/1.03  
% 2.87/1.03  ------  iProver source info
% 2.87/1.03  
% 2.87/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.87/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/1.03  git: non_committed_changes: false
% 2.87/1.03  git: last_make_outside_of_git: false
% 2.87/1.03  
% 2.87/1.03  ------ 
% 2.87/1.03  
% 2.87/1.03  ------ Input Options
% 2.87/1.03  
% 2.87/1.03  --out_options                           all
% 2.87/1.03  --tptp_safe_out                         true
% 2.87/1.03  --problem_path                          ""
% 2.87/1.03  --include_path                          ""
% 2.87/1.03  --clausifier                            res/vclausify_rel
% 2.87/1.03  --clausifier_options                    --mode clausify
% 2.87/1.03  --stdin                                 false
% 2.87/1.03  --stats_out                             all
% 2.87/1.03  
% 2.87/1.03  ------ General Options
% 2.87/1.03  
% 2.87/1.03  --fof                                   false
% 2.87/1.03  --time_out_real                         305.
% 2.87/1.03  --time_out_virtual                      -1.
% 2.87/1.03  --symbol_type_check                     false
% 2.87/1.03  --clausify_out                          false
% 2.87/1.03  --sig_cnt_out                           false
% 2.87/1.03  --trig_cnt_out                          false
% 2.87/1.03  --trig_cnt_out_tolerance                1.
% 2.87/1.03  --trig_cnt_out_sk_spl                   false
% 2.87/1.03  --abstr_cl_out                          false
% 2.87/1.03  
% 2.87/1.03  ------ Global Options
% 2.87/1.03  
% 2.87/1.03  --schedule                              default
% 2.87/1.03  --add_important_lit                     false
% 2.87/1.03  --prop_solver_per_cl                    1000
% 2.87/1.03  --min_unsat_core                        false
% 2.87/1.03  --soft_assumptions                      false
% 2.87/1.03  --soft_lemma_size                       3
% 2.87/1.03  --prop_impl_unit_size                   0
% 2.87/1.03  --prop_impl_unit                        []
% 2.87/1.03  --share_sel_clauses                     true
% 2.87/1.03  --reset_solvers                         false
% 2.87/1.03  --bc_imp_inh                            [conj_cone]
% 2.87/1.03  --conj_cone_tolerance                   3.
% 2.87/1.03  --extra_neg_conj                        none
% 2.87/1.03  --large_theory_mode                     true
% 2.87/1.03  --prolific_symb_bound                   200
% 2.87/1.03  --lt_threshold                          2000
% 2.87/1.03  --clause_weak_htbl                      true
% 2.87/1.03  --gc_record_bc_elim                     false
% 2.87/1.03  
% 2.87/1.03  ------ Preprocessing Options
% 2.87/1.03  
% 2.87/1.03  --preprocessing_flag                    true
% 2.87/1.03  --time_out_prep_mult                    0.1
% 2.87/1.03  --splitting_mode                        input
% 2.87/1.03  --splitting_grd                         true
% 2.87/1.03  --splitting_cvd                         false
% 2.87/1.03  --splitting_cvd_svl                     false
% 2.87/1.03  --splitting_nvd                         32
% 2.87/1.03  --sub_typing                            true
% 2.87/1.03  --prep_gs_sim                           true
% 2.87/1.03  --prep_unflatten                        true
% 2.87/1.03  --prep_res_sim                          true
% 2.87/1.03  --prep_upred                            true
% 2.87/1.03  --prep_sem_filter                       exhaustive
% 2.87/1.03  --prep_sem_filter_out                   false
% 2.87/1.03  --pred_elim                             true
% 2.87/1.03  --res_sim_input                         true
% 2.87/1.03  --eq_ax_congr_red                       true
% 2.87/1.03  --pure_diseq_elim                       true
% 2.87/1.03  --brand_transform                       false
% 2.87/1.03  --non_eq_to_eq                          false
% 2.87/1.03  --prep_def_merge                        true
% 2.87/1.03  --prep_def_merge_prop_impl              false
% 2.87/1.03  --prep_def_merge_mbd                    true
% 2.87/1.03  --prep_def_merge_tr_red                 false
% 2.87/1.03  --prep_def_merge_tr_cl                  false
% 2.87/1.03  --smt_preprocessing                     true
% 2.87/1.03  --smt_ac_axioms                         fast
% 2.87/1.03  --preprocessed_out                      false
% 2.87/1.03  --preprocessed_stats                    false
% 2.87/1.03  
% 2.87/1.03  ------ Abstraction refinement Options
% 2.87/1.03  
% 2.87/1.03  --abstr_ref                             []
% 2.87/1.03  --abstr_ref_prep                        false
% 2.87/1.03  --abstr_ref_until_sat                   false
% 2.87/1.03  --abstr_ref_sig_restrict                funpre
% 2.87/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.03  --abstr_ref_under                       []
% 2.87/1.03  
% 2.87/1.03  ------ SAT Options
% 2.87/1.03  
% 2.87/1.03  --sat_mode                              false
% 2.87/1.03  --sat_fm_restart_options                ""
% 2.87/1.03  --sat_gr_def                            false
% 2.87/1.03  --sat_epr_types                         true
% 2.87/1.03  --sat_non_cyclic_types                  false
% 2.87/1.03  --sat_finite_models                     false
% 2.87/1.03  --sat_fm_lemmas                         false
% 2.87/1.03  --sat_fm_prep                           false
% 2.87/1.03  --sat_fm_uc_incr                        true
% 2.87/1.03  --sat_out_model                         small
% 2.87/1.03  --sat_out_clauses                       false
% 2.87/1.03  
% 2.87/1.03  ------ QBF Options
% 2.87/1.03  
% 2.87/1.03  --qbf_mode                              false
% 2.87/1.03  --qbf_elim_univ                         false
% 2.87/1.03  --qbf_dom_inst                          none
% 2.87/1.03  --qbf_dom_pre_inst                      false
% 2.87/1.03  --qbf_sk_in                             false
% 2.87/1.03  --qbf_pred_elim                         true
% 2.87/1.03  --qbf_split                             512
% 2.87/1.03  
% 2.87/1.03  ------ BMC1 Options
% 2.87/1.03  
% 2.87/1.03  --bmc1_incremental                      false
% 2.87/1.03  --bmc1_axioms                           reachable_all
% 2.87/1.03  --bmc1_min_bound                        0
% 2.87/1.03  --bmc1_max_bound                        -1
% 2.87/1.03  --bmc1_max_bound_default                -1
% 2.87/1.03  --bmc1_symbol_reachability              true
% 2.87/1.03  --bmc1_property_lemmas                  false
% 2.87/1.03  --bmc1_k_induction                      false
% 2.87/1.03  --bmc1_non_equiv_states                 false
% 2.87/1.03  --bmc1_deadlock                         false
% 2.87/1.03  --bmc1_ucm                              false
% 2.87/1.03  --bmc1_add_unsat_core                   none
% 2.87/1.03  --bmc1_unsat_core_children              false
% 2.87/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.03  --bmc1_out_stat                         full
% 2.87/1.03  --bmc1_ground_init                      false
% 2.87/1.03  --bmc1_pre_inst_next_state              false
% 2.87/1.03  --bmc1_pre_inst_state                   false
% 2.87/1.03  --bmc1_pre_inst_reach_state             false
% 2.87/1.03  --bmc1_out_unsat_core                   false
% 2.87/1.03  --bmc1_aig_witness_out                  false
% 2.87/1.03  --bmc1_verbose                          false
% 2.87/1.03  --bmc1_dump_clauses_tptp                false
% 2.87/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.03  --bmc1_dump_file                        -
% 2.87/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.03  --bmc1_ucm_extend_mode                  1
% 2.87/1.03  --bmc1_ucm_init_mode                    2
% 2.87/1.03  --bmc1_ucm_cone_mode                    none
% 2.87/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.03  --bmc1_ucm_relax_model                  4
% 2.87/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.03  --bmc1_ucm_layered_model                none
% 2.87/1.03  --bmc1_ucm_max_lemma_size               10
% 2.87/1.03  
% 2.87/1.03  ------ AIG Options
% 2.87/1.03  
% 2.87/1.03  --aig_mode                              false
% 2.87/1.03  
% 2.87/1.03  ------ Instantiation Options
% 2.87/1.03  
% 2.87/1.03  --instantiation_flag                    true
% 2.87/1.03  --inst_sos_flag                         false
% 2.87/1.03  --inst_sos_phase                        true
% 2.87/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.03  --inst_lit_sel_side                     num_symb
% 2.87/1.03  --inst_solver_per_active                1400
% 2.87/1.03  --inst_solver_calls_frac                1.
% 2.87/1.03  --inst_passive_queue_type               priority_queues
% 2.87/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.03  --inst_passive_queues_freq              [25;2]
% 2.87/1.03  --inst_dismatching                      true
% 2.87/1.03  --inst_eager_unprocessed_to_passive     true
% 2.87/1.03  --inst_prop_sim_given                   true
% 2.87/1.03  --inst_prop_sim_new                     false
% 2.87/1.03  --inst_subs_new                         false
% 2.87/1.03  --inst_eq_res_simp                      false
% 2.87/1.03  --inst_subs_given                       false
% 2.87/1.03  --inst_orphan_elimination               true
% 2.87/1.03  --inst_learning_loop_flag               true
% 2.87/1.03  --inst_learning_start                   3000
% 2.87/1.03  --inst_learning_factor                  2
% 2.87/1.03  --inst_start_prop_sim_after_learn       3
% 2.87/1.03  --inst_sel_renew                        solver
% 2.87/1.03  --inst_lit_activity_flag                true
% 2.87/1.03  --inst_restr_to_given                   false
% 2.87/1.03  --inst_activity_threshold               500
% 2.87/1.03  --inst_out_proof                        true
% 2.87/1.03  
% 2.87/1.03  ------ Resolution Options
% 2.87/1.03  
% 2.87/1.03  --resolution_flag                       true
% 2.87/1.03  --res_lit_sel                           adaptive
% 2.87/1.03  --res_lit_sel_side                      none
% 2.87/1.03  --res_ordering                          kbo
% 2.87/1.03  --res_to_prop_solver                    active
% 2.87/1.03  --res_prop_simpl_new                    false
% 2.87/1.03  --res_prop_simpl_given                  true
% 2.87/1.03  --res_passive_queue_type                priority_queues
% 2.87/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.03  --res_passive_queues_freq               [15;5]
% 2.87/1.03  --res_forward_subs                      full
% 2.87/1.03  --res_backward_subs                     full
% 2.87/1.03  --res_forward_subs_resolution           true
% 2.87/1.03  --res_backward_subs_resolution          true
% 2.87/1.03  --res_orphan_elimination                true
% 2.87/1.03  --res_time_limit                        2.
% 2.87/1.03  --res_out_proof                         true
% 2.87/1.03  
% 2.87/1.03  ------ Superposition Options
% 2.87/1.03  
% 2.87/1.03  --superposition_flag                    true
% 2.87/1.03  --sup_passive_queue_type                priority_queues
% 2.87/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.03  --demod_completeness_check              fast
% 2.87/1.03  --demod_use_ground                      true
% 2.87/1.03  --sup_to_prop_solver                    passive
% 2.87/1.03  --sup_prop_simpl_new                    true
% 2.87/1.03  --sup_prop_simpl_given                  true
% 2.87/1.03  --sup_fun_splitting                     false
% 2.87/1.03  --sup_smt_interval                      50000
% 2.87/1.03  
% 2.87/1.03  ------ Superposition Simplification Setup
% 2.87/1.03  
% 2.87/1.03  --sup_indices_passive                   []
% 2.87/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.03  --sup_full_bw                           [BwDemod]
% 2.87/1.03  --sup_immed_triv                        [TrivRules]
% 2.87/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.03  --sup_immed_bw_main                     []
% 2.87/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.03  
% 2.87/1.03  ------ Combination Options
% 2.87/1.03  
% 2.87/1.03  --comb_res_mult                         3
% 2.87/1.03  --comb_sup_mult                         2
% 2.87/1.03  --comb_inst_mult                        10
% 2.87/1.03  
% 2.87/1.03  ------ Debug Options
% 2.87/1.03  
% 2.87/1.03  --dbg_backtrace                         false
% 2.87/1.03  --dbg_dump_prop_clauses                 false
% 2.87/1.03  --dbg_dump_prop_clauses_file            -
% 2.87/1.03  --dbg_out_stat                          false
% 2.87/1.03  ------ Parsing...
% 2.87/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/1.03  
% 2.87/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.87/1.03  
% 2.87/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/1.03  
% 2.87/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/1.03  ------ Proving...
% 2.87/1.03  ------ Problem Properties 
% 2.87/1.03  
% 2.87/1.03  
% 2.87/1.03  clauses                                 23
% 2.87/1.03  conjectures                             4
% 2.87/1.03  EPR                                     5
% 2.87/1.03  Horn                                    13
% 2.87/1.03  unary                                   5
% 2.87/1.03  binary                                  8
% 2.87/1.03  lits                                    70
% 2.87/1.03  lits eq                                 6
% 2.87/1.03  fd_pure                                 0
% 2.87/1.03  fd_pseudo                               0
% 2.87/1.03  fd_cond                                 0
% 2.87/1.03  fd_pseudo_cond                          3
% 2.87/1.03  AC symbols                              0
% 2.87/1.03  
% 2.87/1.03  ------ Schedule dynamic 5 is on 
% 2.87/1.03  
% 2.87/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/1.03  
% 2.87/1.03  
% 2.87/1.03  ------ 
% 2.87/1.03  Current options:
% 2.87/1.03  ------ 
% 2.87/1.03  
% 2.87/1.03  ------ Input Options
% 2.87/1.03  
% 2.87/1.03  --out_options                           all
% 2.87/1.03  --tptp_safe_out                         true
% 2.87/1.03  --problem_path                          ""
% 2.87/1.03  --include_path                          ""
% 2.87/1.03  --clausifier                            res/vclausify_rel
% 2.87/1.03  --clausifier_options                    --mode clausify
% 2.87/1.03  --stdin                                 false
% 2.87/1.03  --stats_out                             all
% 2.87/1.03  
% 2.87/1.03  ------ General Options
% 2.87/1.03  
% 2.87/1.03  --fof                                   false
% 2.87/1.03  --time_out_real                         305.
% 2.87/1.03  --time_out_virtual                      -1.
% 2.87/1.03  --symbol_type_check                     false
% 2.87/1.03  --clausify_out                          false
% 2.87/1.03  --sig_cnt_out                           false
% 2.87/1.03  --trig_cnt_out                          false
% 2.87/1.03  --trig_cnt_out_tolerance                1.
% 2.87/1.03  --trig_cnt_out_sk_spl                   false
% 2.87/1.03  --abstr_cl_out                          false
% 2.87/1.03  
% 2.87/1.03  ------ Global Options
% 2.87/1.03  
% 2.87/1.03  --schedule                              default
% 2.87/1.03  --add_important_lit                     false
% 2.87/1.03  --prop_solver_per_cl                    1000
% 2.87/1.03  --min_unsat_core                        false
% 2.87/1.03  --soft_assumptions                      false
% 2.87/1.03  --soft_lemma_size                       3
% 2.87/1.03  --prop_impl_unit_size                   0
% 2.87/1.03  --prop_impl_unit                        []
% 2.87/1.03  --share_sel_clauses                     true
% 2.87/1.03  --reset_solvers                         false
% 2.87/1.03  --bc_imp_inh                            [conj_cone]
% 2.87/1.03  --conj_cone_tolerance                   3.
% 2.87/1.03  --extra_neg_conj                        none
% 2.87/1.03  --large_theory_mode                     true
% 2.87/1.03  --prolific_symb_bound                   200
% 2.87/1.03  --lt_threshold                          2000
% 2.87/1.03  --clause_weak_htbl                      true
% 2.87/1.03  --gc_record_bc_elim                     false
% 2.87/1.03  
% 2.87/1.03  ------ Preprocessing Options
% 2.87/1.03  
% 2.87/1.03  --preprocessing_flag                    true
% 2.87/1.03  --time_out_prep_mult                    0.1
% 2.87/1.03  --splitting_mode                        input
% 2.87/1.03  --splitting_grd                         true
% 2.87/1.03  --splitting_cvd                         false
% 2.87/1.03  --splitting_cvd_svl                     false
% 2.87/1.03  --splitting_nvd                         32
% 2.87/1.03  --sub_typing                            true
% 2.87/1.03  --prep_gs_sim                           true
% 2.87/1.03  --prep_unflatten                        true
% 2.87/1.03  --prep_res_sim                          true
% 2.87/1.03  --prep_upred                            true
% 2.87/1.03  --prep_sem_filter                       exhaustive
% 2.87/1.03  --prep_sem_filter_out                   false
% 2.87/1.03  --pred_elim                             true
% 2.87/1.03  --res_sim_input                         true
% 2.87/1.03  --eq_ax_congr_red                       true
% 2.87/1.03  --pure_diseq_elim                       true
% 2.87/1.03  --brand_transform                       false
% 2.87/1.03  --non_eq_to_eq                          false
% 2.87/1.03  --prep_def_merge                        true
% 2.87/1.03  --prep_def_merge_prop_impl              false
% 2.87/1.03  --prep_def_merge_mbd                    true
% 2.87/1.03  --prep_def_merge_tr_red                 false
% 2.87/1.03  --prep_def_merge_tr_cl                  false
% 2.87/1.03  --smt_preprocessing                     true
% 2.87/1.03  --smt_ac_axioms                         fast
% 2.87/1.03  --preprocessed_out                      false
% 2.87/1.03  --preprocessed_stats                    false
% 2.87/1.03  
% 2.87/1.03  ------ Abstraction refinement Options
% 2.87/1.03  
% 2.87/1.03  --abstr_ref                             []
% 2.87/1.03  --abstr_ref_prep                        false
% 2.87/1.03  --abstr_ref_until_sat                   false
% 2.87/1.03  --abstr_ref_sig_restrict                funpre
% 2.87/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.03  --abstr_ref_under                       []
% 2.87/1.03  
% 2.87/1.03  ------ SAT Options
% 2.87/1.03  
% 2.87/1.03  --sat_mode                              false
% 2.87/1.03  --sat_fm_restart_options                ""
% 2.87/1.03  --sat_gr_def                            false
% 2.87/1.03  --sat_epr_types                         true
% 2.87/1.03  --sat_non_cyclic_types                  false
% 2.87/1.03  --sat_finite_models                     false
% 2.87/1.03  --sat_fm_lemmas                         false
% 2.87/1.03  --sat_fm_prep                           false
% 2.87/1.03  --sat_fm_uc_incr                        true
% 2.87/1.03  --sat_out_model                         small
% 2.87/1.03  --sat_out_clauses                       false
% 2.87/1.03  
% 2.87/1.03  ------ QBF Options
% 2.87/1.03  
% 2.87/1.03  --qbf_mode                              false
% 2.87/1.03  --qbf_elim_univ                         false
% 2.87/1.03  --qbf_dom_inst                          none
% 2.87/1.03  --qbf_dom_pre_inst                      false
% 2.87/1.03  --qbf_sk_in                             false
% 2.87/1.03  --qbf_pred_elim                         true
% 2.87/1.03  --qbf_split                             512
% 2.87/1.03  
% 2.87/1.03  ------ BMC1 Options
% 2.87/1.03  
% 2.87/1.03  --bmc1_incremental                      false
% 2.87/1.03  --bmc1_axioms                           reachable_all
% 2.87/1.03  --bmc1_min_bound                        0
% 2.87/1.03  --bmc1_max_bound                        -1
% 2.87/1.03  --bmc1_max_bound_default                -1
% 2.87/1.03  --bmc1_symbol_reachability              true
% 2.87/1.03  --bmc1_property_lemmas                  false
% 2.87/1.03  --bmc1_k_induction                      false
% 2.87/1.03  --bmc1_non_equiv_states                 false
% 2.87/1.03  --bmc1_deadlock                         false
% 2.87/1.03  --bmc1_ucm                              false
% 2.87/1.03  --bmc1_add_unsat_core                   none
% 2.87/1.03  --bmc1_unsat_core_children              false
% 2.87/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.03  --bmc1_out_stat                         full
% 2.87/1.03  --bmc1_ground_init                      false
% 2.87/1.03  --bmc1_pre_inst_next_state              false
% 2.87/1.03  --bmc1_pre_inst_state                   false
% 2.87/1.03  --bmc1_pre_inst_reach_state             false
% 2.87/1.03  --bmc1_out_unsat_core                   false
% 2.87/1.03  --bmc1_aig_witness_out                  false
% 2.87/1.03  --bmc1_verbose                          false
% 2.87/1.03  --bmc1_dump_clauses_tptp                false
% 2.87/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.03  --bmc1_dump_file                        -
% 2.87/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.03  --bmc1_ucm_extend_mode                  1
% 2.87/1.03  --bmc1_ucm_init_mode                    2
% 2.87/1.03  --bmc1_ucm_cone_mode                    none
% 2.87/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.03  --bmc1_ucm_relax_model                  4
% 2.87/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.03  --bmc1_ucm_layered_model                none
% 2.87/1.03  --bmc1_ucm_max_lemma_size               10
% 2.87/1.03  
% 2.87/1.03  ------ AIG Options
% 2.87/1.03  
% 2.87/1.03  --aig_mode                              false
% 2.87/1.03  
% 2.87/1.03  ------ Instantiation Options
% 2.87/1.03  
% 2.87/1.03  --instantiation_flag                    true
% 2.87/1.03  --inst_sos_flag                         false
% 2.87/1.03  --inst_sos_phase                        true
% 2.87/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.03  --inst_lit_sel_side                     none
% 2.87/1.03  --inst_solver_per_active                1400
% 2.87/1.03  --inst_solver_calls_frac                1.
% 2.87/1.03  --inst_passive_queue_type               priority_queues
% 2.87/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.03  --inst_passive_queues_freq              [25;2]
% 2.87/1.03  --inst_dismatching                      true
% 2.87/1.03  --inst_eager_unprocessed_to_passive     true
% 2.87/1.03  --inst_prop_sim_given                   true
% 2.87/1.03  --inst_prop_sim_new                     false
% 2.87/1.03  --inst_subs_new                         false
% 2.87/1.03  --inst_eq_res_simp                      false
% 2.87/1.03  --inst_subs_given                       false
% 2.87/1.03  --inst_orphan_elimination               true
% 2.87/1.03  --inst_learning_loop_flag               true
% 2.87/1.03  --inst_learning_start                   3000
% 2.87/1.03  --inst_learning_factor                  2
% 2.87/1.03  --inst_start_prop_sim_after_learn       3
% 2.87/1.03  --inst_sel_renew                        solver
% 2.87/1.03  --inst_lit_activity_flag                true
% 2.87/1.03  --inst_restr_to_given                   false
% 2.87/1.03  --inst_activity_threshold               500
% 2.87/1.03  --inst_out_proof                        true
% 2.87/1.03  
% 2.87/1.03  ------ Resolution Options
% 2.87/1.03  
% 2.87/1.03  --resolution_flag                       false
% 2.87/1.03  --res_lit_sel                           adaptive
% 2.87/1.03  --res_lit_sel_side                      none
% 2.87/1.03  --res_ordering                          kbo
% 2.87/1.03  --res_to_prop_solver                    active
% 2.87/1.03  --res_prop_simpl_new                    false
% 2.87/1.03  --res_prop_simpl_given                  true
% 2.87/1.03  --res_passive_queue_type                priority_queues
% 2.87/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.03  --res_passive_queues_freq               [15;5]
% 2.87/1.03  --res_forward_subs                      full
% 2.87/1.03  --res_backward_subs                     full
% 2.87/1.03  --res_forward_subs_resolution           true
% 2.87/1.03  --res_backward_subs_resolution          true
% 2.87/1.03  --res_orphan_elimination                true
% 2.87/1.03  --res_time_limit                        2.
% 2.87/1.03  --res_out_proof                         true
% 2.87/1.03  
% 2.87/1.03  ------ Superposition Options
% 2.87/1.03  
% 2.87/1.03  --superposition_flag                    true
% 2.87/1.03  --sup_passive_queue_type                priority_queues
% 2.87/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.03  --demod_completeness_check              fast
% 2.87/1.03  --demod_use_ground                      true
% 2.87/1.03  --sup_to_prop_solver                    passive
% 2.87/1.03  --sup_prop_simpl_new                    true
% 2.87/1.03  --sup_prop_simpl_given                  true
% 2.87/1.03  --sup_fun_splitting                     false
% 2.87/1.03  --sup_smt_interval                      50000
% 2.87/1.03  
% 2.87/1.03  ------ Superposition Simplification Setup
% 2.87/1.03  
% 2.87/1.03  --sup_indices_passive                   []
% 2.87/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.03  --sup_full_bw                           [BwDemod]
% 2.87/1.03  --sup_immed_triv                        [TrivRules]
% 2.87/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.03  --sup_immed_bw_main                     []
% 2.87/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.03  
% 2.87/1.03  ------ Combination Options
% 2.87/1.03  
% 2.87/1.03  --comb_res_mult                         3
% 2.87/1.03  --comb_sup_mult                         2
% 2.87/1.03  --comb_inst_mult                        10
% 2.87/1.03  
% 2.87/1.03  ------ Debug Options
% 2.87/1.03  
% 2.87/1.03  --dbg_backtrace                         false
% 2.87/1.03  --dbg_dump_prop_clauses                 false
% 2.87/1.03  --dbg_dump_prop_clauses_file            -
% 2.87/1.03  --dbg_out_stat                          false
% 2.87/1.03  
% 2.87/1.03  
% 2.87/1.03  
% 2.87/1.03  
% 2.87/1.03  ------ Proving...
% 2.87/1.03  
% 2.87/1.03  
% 2.87/1.03  % SZS status Theorem for theBenchmark.p
% 2.87/1.03  
% 2.87/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/1.03  
% 2.87/1.03  fof(f1,axiom,(
% 2.87/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/1.03  
% 2.87/1.03  fof(f22,plain,(
% 2.87/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.87/1.03    inference(nnf_transformation,[],[f1])).
% 2.87/1.03  
% 2.87/1.03  fof(f23,plain,(
% 2.87/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.87/1.03    inference(flattening,[],[f22])).
% 2.87/1.03  
% 2.87/1.03  fof(f24,plain,(
% 2.87/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.87/1.03    inference(rectify,[],[f23])).
% 2.87/1.03  
% 2.87/1.03  fof(f25,plain,(
% 2.87/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.87/1.03    introduced(choice_axiom,[])).
% 2.87/1.03  
% 2.87/1.03  fof(f26,plain,(
% 2.87/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.87/1.03  
% 2.87/1.03  fof(f46,plain,(
% 2.87/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f26])).
% 2.87/1.03  
% 2.87/1.03  fof(f6,axiom,(
% 2.87/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/1.03  
% 2.87/1.03  fof(f57,plain,(
% 2.87/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f6])).
% 2.87/1.03  
% 2.87/1.03  fof(f72,plain,(
% 2.87/1.03    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.87/1.03    inference(definition_unfolding,[],[f46,f57])).
% 2.87/1.03  
% 2.87/1.03  fof(f2,axiom,(
% 2.87/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/1.03  
% 2.87/1.03  fof(f11,plain,(
% 2.87/1.03    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.87/1.03    inference(rectify,[],[f2])).
% 2.87/1.03  
% 2.87/1.03  fof(f14,plain,(
% 2.87/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.87/1.03    inference(ennf_transformation,[],[f11])).
% 2.87/1.03  
% 2.87/1.03  fof(f27,plain,(
% 2.87/1.03    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.87/1.03    introduced(choice_axiom,[])).
% 2.87/1.03  
% 2.87/1.03  fof(f28,plain,(
% 2.87/1.03    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f27])).
% 2.87/1.03  
% 2.87/1.03  fof(f51,plain,(
% 2.87/1.03    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f28])).
% 2.87/1.03  
% 2.87/1.03  fof(f8,axiom,(
% 2.87/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 2.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/1.03  
% 2.87/1.03  fof(f18,plain,(
% 2.87/1.03    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.87/1.03    inference(ennf_transformation,[],[f8])).
% 2.87/1.03  
% 2.87/1.03  fof(f19,plain,(
% 2.87/1.03    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.87/1.03    inference(flattening,[],[f18])).
% 2.87/1.03  
% 2.87/1.03  fof(f39,plain,(
% 2.87/1.03    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.87/1.03    inference(nnf_transformation,[],[f19])).
% 2.87/1.03  
% 2.87/1.03  fof(f64,plain,(
% 2.87/1.03    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f39])).
% 2.87/1.03  
% 2.87/1.03  fof(f9,conjecture,(
% 2.87/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 2.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/1.03  
% 2.87/1.03  fof(f10,negated_conjecture,(
% 2.87/1.03    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 2.87/1.03    inference(negated_conjecture,[],[f9])).
% 2.87/1.03  
% 2.87/1.03  fof(f12,plain,(
% 2.87/1.03    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 2.87/1.03    inference(pure_predicate_removal,[],[f10])).
% 2.87/1.03  
% 2.87/1.03  fof(f13,plain,(
% 2.87/1.03    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 2.87/1.03    inference(pure_predicate_removal,[],[f12])).
% 2.87/1.03  
% 2.87/1.03  fof(f20,plain,(
% 2.87/1.03    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.87/1.03    inference(ennf_transformation,[],[f13])).
% 2.87/1.03  
% 2.87/1.03  fof(f21,plain,(
% 2.87/1.03    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.87/1.03    inference(flattening,[],[f20])).
% 2.87/1.03  
% 2.87/1.03  fof(f41,plain,(
% 2.87/1.03    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK7,u1_struct_0(X0)) & l1_waybel_0(sK7,X0) & ~v2_struct_0(sK7))) )),
% 2.87/1.03    introduced(choice_axiom,[])).
% 2.87/1.03  
% 2.87/1.03  fof(f40,plain,(
% 2.87/1.03    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK6,X1,u1_struct_0(sK6)) & l1_waybel_0(X1,sK6) & ~v2_struct_0(X1)) & l1_struct_0(sK6) & ~v2_struct_0(sK6))),
% 2.87/1.03    introduced(choice_axiom,[])).
% 2.87/1.03  
% 2.87/1.03  fof(f42,plain,(
% 2.87/1.03    (~r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) & l1_waybel_0(sK7,sK6) & ~v2_struct_0(sK7)) & l1_struct_0(sK6) & ~v2_struct_0(sK6)),
% 2.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f21,f41,f40])).
% 2.87/1.03  
% 2.87/1.03  fof(f69,plain,(
% 2.87/1.03    ~r1_waybel_0(sK6,sK7,u1_struct_0(sK6))),
% 2.87/1.03    inference(cnf_transformation,[],[f42])).
% 2.87/1.03  
% 2.87/1.03  fof(f65,plain,(
% 2.87/1.03    ~v2_struct_0(sK6)),
% 2.87/1.03    inference(cnf_transformation,[],[f42])).
% 2.87/1.03  
% 2.87/1.03  fof(f66,plain,(
% 2.87/1.03    l1_struct_0(sK6)),
% 2.87/1.03    inference(cnf_transformation,[],[f42])).
% 2.87/1.03  
% 2.87/1.03  fof(f67,plain,(
% 2.87/1.03    ~v2_struct_0(sK7)),
% 2.87/1.03    inference(cnf_transformation,[],[f42])).
% 2.87/1.03  
% 2.87/1.03  fof(f68,plain,(
% 2.87/1.03    l1_waybel_0(sK7,sK6)),
% 2.87/1.03    inference(cnf_transformation,[],[f42])).
% 2.87/1.03  
% 2.87/1.03  fof(f43,plain,(
% 2.87/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.87/1.03    inference(cnf_transformation,[],[f26])).
% 2.87/1.03  
% 2.87/1.03  fof(f75,plain,(
% 2.87/1.03    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 2.87/1.03    inference(definition_unfolding,[],[f43,f57])).
% 2.87/1.03  
% 2.87/1.03  fof(f80,plain,(
% 2.87/1.03    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 2.87/1.03    inference(equality_resolution,[],[f75])).
% 2.87/1.03  
% 2.87/1.03  fof(f7,axiom,(
% 2.87/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 2.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/1.03  
% 2.87/1.03  fof(f16,plain,(
% 2.87/1.03    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.87/1.03    inference(ennf_transformation,[],[f7])).
% 2.87/1.03  
% 2.87/1.03  fof(f17,plain,(
% 2.87/1.03    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.87/1.03    inference(flattening,[],[f16])).
% 2.87/1.03  
% 2.87/1.03  fof(f34,plain,(
% 2.87/1.03    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.87/1.03    inference(nnf_transformation,[],[f17])).
% 2.87/1.03  
% 2.87/1.03  fof(f35,plain,(
% 2.87/1.03    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.87/1.03    inference(rectify,[],[f34])).
% 2.87/1.03  
% 2.87/1.03  fof(f37,plain,(
% 2.87/1.03    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5)) & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))))),
% 2.87/1.03    introduced(choice_axiom,[])).
% 2.87/1.03  
% 2.87/1.03  fof(f36,plain,(
% 2.87/1.03    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK4(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 2.87/1.03    introduced(choice_axiom,[])).
% 2.87/1.03  
% 2.87/1.03  fof(f38,plain,(
% 2.87/1.03    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK4(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5)) & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f35,f37,f36])).
% 2.87/1.03  
% 2.87/1.03  fof(f60,plain,(
% 2.87/1.03    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f38])).
% 2.87/1.03  
% 2.87/1.03  fof(f49,plain,(
% 2.87/1.03    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f28])).
% 2.87/1.03  
% 2.87/1.03  fof(f50,plain,(
% 2.87/1.03    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f28])).
% 2.87/1.03  
% 2.87/1.03  fof(f44,plain,(
% 2.87/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.87/1.03    inference(cnf_transformation,[],[f26])).
% 2.87/1.03  
% 2.87/1.03  fof(f74,plain,(
% 2.87/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 2.87/1.03    inference(definition_unfolding,[],[f44,f57])).
% 2.87/1.03  
% 2.87/1.03  fof(f79,plain,(
% 2.87/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 2.87/1.03    inference(equality_resolution,[],[f74])).
% 2.87/1.03  
% 2.87/1.03  fof(f48,plain,(
% 2.87/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f26])).
% 2.87/1.03  
% 2.87/1.03  fof(f70,plain,(
% 2.87/1.03    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.87/1.03    inference(definition_unfolding,[],[f48,f57])).
% 2.87/1.03  
% 2.87/1.03  fof(f5,axiom,(
% 2.87/1.03    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.87/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/1.03  
% 2.87/1.03  fof(f32,plain,(
% 2.87/1.03    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 2.87/1.03    introduced(choice_axiom,[])).
% 2.87/1.03  
% 2.87/1.03  fof(f33,plain,(
% 2.87/1.03    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 2.87/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f32])).
% 2.87/1.03  
% 2.87/1.03  fof(f56,plain,(
% 2.87/1.03    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 2.87/1.03    inference(cnf_transformation,[],[f33])).
% 2.87/1.03  
% 2.87/1.03  cnf(c_2,plain,
% 2.87/1.03      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.87/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.87/1.03      | k6_subset_1(X0,X1) = X2 ),
% 2.87/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1625,plain,
% 2.87/1.03      ( r2_hidden(sK0(u1_struct_0(sK6),X0,u1_struct_0(sK6)),u1_struct_0(sK6))
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),X0) = u1_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_6648,plain,
% 2.87/1.03      ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),u1_struct_0(sK6))
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),k6_subset_1(X0,X1)) = u1_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_1625]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_6650,plain,
% 2.87/1.03      ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),u1_struct_0(sK6))
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),k6_subset_1(sK6,sK6)) = u1_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_6648]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_6,plain,
% 2.87/1.03      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 2.87/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_3395,plain,
% 2.87/1.03      ( ~ r1_xboole_0(X0,X1)
% 2.87/1.03      | ~ r2_hidden(k2_waybel_0(X2,sK7,sK5(X2,sK7,X1,sK3(u1_struct_0(sK7)))),X1)
% 2.87/1.03      | ~ r2_hidden(k2_waybel_0(X2,sK7,sK5(X2,sK7,X1,sK3(u1_struct_0(sK7)))),X0) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_5975,plain,
% 2.87/1.03      ( ~ r1_xboole_0(X0,k6_subset_1(X1,X2))
% 2.87/1.03      | ~ r2_hidden(k2_waybel_0(X3,sK7,sK5(X3,sK7,k6_subset_1(X1,X2),sK3(u1_struct_0(sK7)))),X0)
% 2.87/1.03      | ~ r2_hidden(k2_waybel_0(X3,sK7,sK5(X3,sK7,k6_subset_1(X1,X2),sK3(u1_struct_0(sK7)))),k6_subset_1(X1,X2)) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_3395]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_5977,plain,
% 2.87/1.03      ( ~ r1_xboole_0(sK6,k6_subset_1(sK6,sK6))
% 2.87/1.03      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),k6_subset_1(sK6,sK6))
% 2.87/1.03      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_5975]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1895,plain,
% 2.87/1.03      ( ~ r1_xboole_0(X0,X1)
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),X1,u1_struct_0(sK6)),X0)
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),X1,u1_struct_0(sK6)),X1) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_5360,plain,
% 2.87/1.03      ( ~ r1_xboole_0(X0,k6_subset_1(X1,X2))
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X1,X2),u1_struct_0(sK6)),X0)
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X1,X2),u1_struct_0(sK6)),k6_subset_1(X1,X2)) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_1895]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_5365,plain,
% 2.87/1.03      ( ~ r1_xboole_0(sK6,k6_subset_1(sK6,sK6))
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),k6_subset_1(sK6,sK6))
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_5360]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_19,plain,
% 2.87/1.03      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 2.87/1.03      | r2_waybel_0(X0,X1,X2)
% 2.87/1.03      | ~ l1_waybel_0(X1,X0)
% 2.87/1.03      | ~ l1_struct_0(X0)
% 2.87/1.03      | v2_struct_0(X0)
% 2.87/1.03      | v2_struct_0(X1) ),
% 2.87/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_21,negated_conjecture,
% 2.87/1.03      ( ~ r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) ),
% 2.87/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_472,plain,
% 2.87/1.03      ( r2_waybel_0(X0,X1,X2)
% 2.87/1.03      | ~ l1_waybel_0(X1,X0)
% 2.87/1.03      | ~ l1_struct_0(X0)
% 2.87/1.03      | v2_struct_0(X0)
% 2.87/1.03      | v2_struct_0(X1)
% 2.87/1.03      | k6_subset_1(u1_struct_0(X0),X2) != u1_struct_0(sK6)
% 2.87/1.03      | sK7 != X1
% 2.87/1.03      | sK6 != X0 ),
% 2.87/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_473,plain,
% 2.87/1.03      ( r2_waybel_0(sK6,sK7,X0)
% 2.87/1.03      | ~ l1_waybel_0(sK7,sK6)
% 2.87/1.03      | ~ l1_struct_0(sK6)
% 2.87/1.03      | v2_struct_0(sK7)
% 2.87/1.03      | v2_struct_0(sK6)
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),X0) != u1_struct_0(sK6) ),
% 2.87/1.03      inference(unflattening,[status(thm)],[c_472]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_25,negated_conjecture,
% 2.87/1.03      ( ~ v2_struct_0(sK6) ),
% 2.87/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_24,negated_conjecture,
% 2.87/1.03      ( l1_struct_0(sK6) ),
% 2.87/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_23,negated_conjecture,
% 2.87/1.03      ( ~ v2_struct_0(sK7) ),
% 2.87/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_22,negated_conjecture,
% 2.87/1.03      ( l1_waybel_0(sK7,sK6) ),
% 2.87/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_477,plain,
% 2.87/1.03      ( r2_waybel_0(sK6,sK7,X0)
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),X0) != u1_struct_0(sK6) ),
% 2.87/1.03      inference(global_propositional_subsumption,
% 2.87/1.03                [status(thm)],
% 2.87/1.03                [c_473,c_25,c_24,c_23,c_22]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_4249,plain,
% 2.87/1.03      ( r2_waybel_0(sK6,sK7,k6_subset_1(X0,X1))
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),k6_subset_1(X0,X1)) != u1_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_477]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_4256,plain,
% 2.87/1.03      ( r2_waybel_0(sK6,sK7,k6_subset_1(sK6,sK6))
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),k6_subset_1(sK6,sK6)) != u1_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_4249]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_5,plain,
% 2.87/1.03      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 2.87/1.03      inference(cnf_transformation,[],[f80]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_3388,plain,
% 2.87/1.03      ( r2_hidden(k2_waybel_0(X0,sK7,sK5(X0,sK7,k6_subset_1(X1,X2),sK3(u1_struct_0(sK7)))),X1)
% 2.87/1.03      | ~ r2_hidden(k2_waybel_0(X0,sK7,sK5(X0,sK7,k6_subset_1(X1,X2),sK3(u1_struct_0(sK7)))),k6_subset_1(X1,X2)) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_3392,plain,
% 2.87/1.03      ( ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),k6_subset_1(sK6,sK6))
% 2.87/1.03      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_3388]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_16,plain,
% 2.87/1.03      ( ~ r2_waybel_0(X0,X1,X2)
% 2.87/1.03      | ~ l1_waybel_0(X1,X0)
% 2.87/1.03      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 2.87/1.03      | r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2)
% 2.87/1.03      | ~ l1_struct_0(X0)
% 2.87/1.03      | v2_struct_0(X0)
% 2.87/1.03      | v2_struct_0(X1) ),
% 2.87/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1591,plain,
% 2.87/1.03      ( ~ r2_waybel_0(sK6,sK7,X0)
% 2.87/1.03      | ~ l1_waybel_0(sK7,sK6)
% 2.87/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.87/1.03      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,X1)),X0)
% 2.87/1.03      | ~ l1_struct_0(sK6)
% 2.87/1.03      | v2_struct_0(sK7)
% 2.87/1.03      | v2_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_2107,plain,
% 2.87/1.03      ( ~ r2_waybel_0(sK6,sK7,X0)
% 2.87/1.03      | ~ l1_waybel_0(sK7,sK6)
% 2.87/1.03      | ~ m1_subset_1(sK3(X1),u1_struct_0(sK7))
% 2.87/1.03      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(X1))),X0)
% 2.87/1.03      | ~ l1_struct_0(sK6)
% 2.87/1.03      | v2_struct_0(sK7)
% 2.87/1.03      | v2_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_1591]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_2241,plain,
% 2.87/1.03      ( ~ r2_waybel_0(sK6,sK7,k6_subset_1(X0,X1))
% 2.87/1.03      | ~ l1_waybel_0(sK7,sK6)
% 2.87/1.03      | ~ m1_subset_1(sK3(X2),u1_struct_0(sK7))
% 2.87/1.03      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(X0,X1),sK3(X2))),k6_subset_1(X0,X1))
% 2.87/1.03      | ~ l1_struct_0(sK6)
% 2.87/1.03      | v2_struct_0(sK7)
% 2.87/1.03      | v2_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_2107]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_3326,plain,
% 2.87/1.03      ( ~ r2_waybel_0(sK6,sK7,k6_subset_1(X0,X1))
% 2.87/1.03      | ~ l1_waybel_0(sK7,sK6)
% 2.87/1.03      | ~ m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7))
% 2.87/1.03      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(X0,X1),sK3(u1_struct_0(sK7)))),k6_subset_1(X0,X1))
% 2.87/1.03      | ~ l1_struct_0(sK6)
% 2.87/1.03      | v2_struct_0(sK7)
% 2.87/1.03      | v2_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_2241]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_3328,plain,
% 2.87/1.03      ( ~ r2_waybel_0(sK6,sK7,k6_subset_1(sK6,sK6))
% 2.87/1.03      | ~ l1_waybel_0(sK7,sK6)
% 2.87/1.03      | ~ m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7))
% 2.87/1.03      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,k6_subset_1(sK6,sK6),sK3(u1_struct_0(sK7)))),k6_subset_1(sK6,sK6))
% 2.87/1.03      | ~ l1_struct_0(sK6)
% 2.87/1.03      | v2_struct_0(sK7)
% 2.87/1.03      | v2_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_3326]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_8,plain,
% 2.87/1.03      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.87/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1371,plain,
% 2.87/1.03      ( r1_xboole_0(X0,X1) = iProver_top
% 2.87/1.03      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.87/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_7,plain,
% 2.87/1.03      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 2.87/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1372,plain,
% 2.87/1.03      ( r1_xboole_0(X0,X1) = iProver_top
% 2.87/1.03      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 2.87/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_4,plain,
% 2.87/1.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
% 2.87/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1375,plain,
% 2.87/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.87/1.03      | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
% 2.87/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1979,plain,
% 2.87/1.03      ( r1_xboole_0(X0,k6_subset_1(X1,X2)) = iProver_top
% 2.87/1.03      | r2_hidden(sK1(X0,k6_subset_1(X1,X2)),X2) != iProver_top ),
% 2.87/1.03      inference(superposition,[status(thm)],[c_1372,c_1375]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_2092,plain,
% 2.87/1.03      ( r1_xboole_0(X0,k6_subset_1(X1,X0)) = iProver_top ),
% 2.87/1.03      inference(superposition,[status(thm)],[c_1371,c_1979]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_2093,plain,
% 2.87/1.03      ( r1_xboole_0(X0,k6_subset_1(X1,X0)) ),
% 2.87/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_2092]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_2095,plain,
% 2.87/1.03      ( r1_xboole_0(sK6,k6_subset_1(sK6,sK6)) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_2093]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1886,plain,
% 2.87/1.03      ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),X0)
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),k6_subset_1(X0,X1)) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1892,plain,
% 2.87/1.03      ( ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),k6_subset_1(sK6,sK6))
% 2.87/1.03      | r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_1886]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_0,plain,
% 2.87/1.03      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.87/1.03      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.87/1.03      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.87/1.03      | k6_subset_1(X0,X1) = X2 ),
% 2.87/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1630,plain,
% 2.87/1.03      ( r2_hidden(sK0(u1_struct_0(sK6),X0,u1_struct_0(sK6)),X0)
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),X0,u1_struct_0(sK6)),u1_struct_0(sK6))
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),X0) = u1_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1885,plain,
% 2.87/1.03      ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),k6_subset_1(X0,X1))
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(X0,X1),u1_struct_0(sK6)),u1_struct_0(sK6))
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),k6_subset_1(X0,X1)) = u1_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_1630]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1888,plain,
% 2.87/1.03      ( r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),k6_subset_1(sK6,sK6))
% 2.87/1.03      | ~ r2_hidden(sK0(u1_struct_0(sK6),k6_subset_1(sK6,sK6),u1_struct_0(sK6)),u1_struct_0(sK6))
% 2.87/1.03      | k6_subset_1(u1_struct_0(sK6),k6_subset_1(sK6,sK6)) = u1_struct_0(sK6) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_1885]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_13,plain,
% 2.87/1.03      ( m1_subset_1(sK3(X0),X0) ),
% 2.87/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(c_1666,plain,
% 2.87/1.03      ( m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
% 2.87/1.03      inference(instantiation,[status(thm)],[c_13]) ).
% 2.87/1.03  
% 2.87/1.03  cnf(contradiction,plain,
% 2.87/1.03      ( $false ),
% 2.87/1.03      inference(minisat,
% 2.87/1.03                [status(thm)],
% 2.87/1.03                [c_6650,c_5977,c_5365,c_4256,c_3392,c_3328,c_2095,c_1892,
% 2.87/1.03                 c_1888,c_1666,c_22,c_23,c_24,c_25]) ).
% 2.87/1.03  
% 2.87/1.03  
% 2.87/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.03  
% 2.87/1.03  ------                               Statistics
% 2.87/1.03  
% 2.87/1.03  ------ General
% 2.87/1.03  
% 2.87/1.03  abstr_ref_over_cycles:                  0
% 2.87/1.03  abstr_ref_under_cycles:                 0
% 2.87/1.03  gc_basic_clause_elim:                   0
% 2.87/1.03  forced_gc_time:                         0
% 2.87/1.03  parsing_time:                           0.012
% 2.87/1.03  unif_index_cands_time:                  0.
% 2.87/1.03  unif_index_add_time:                    0.
% 2.87/1.03  orderings_time:                         0.
% 2.87/1.03  out_proof_time:                         0.025
% 2.87/1.03  total_time:                             0.311
% 2.87/1.03  num_of_symbols:                         51
% 2.87/1.03  num_of_terms:                           6135
% 2.87/1.03  
% 2.87/1.03  ------ Preprocessing
% 2.87/1.03  
% 2.87/1.03  num_of_splits:                          0
% 2.87/1.03  num_of_split_atoms:                     0
% 2.87/1.03  num_of_reused_defs:                     0
% 2.87/1.03  num_eq_ax_congr_red:                    61
% 2.87/1.03  num_of_sem_filtered_clauses:            1
% 2.87/1.03  num_of_subtypes:                        0
% 2.87/1.03  monotx_restored_types:                  0
% 2.87/1.03  sat_num_of_epr_types:                   0
% 2.87/1.03  sat_num_of_non_cyclic_types:            0
% 2.87/1.03  sat_guarded_non_collapsed_types:        0
% 2.87/1.03  num_pure_diseq_elim:                    0
% 2.87/1.03  simp_replaced_by:                       0
% 2.87/1.03  res_preprocessed:                       120
% 2.87/1.03  prep_upred:                             0
% 2.87/1.03  prep_unflattend:                        5
% 2.87/1.03  smt_new_axioms:                         0
% 2.87/1.03  pred_elim_cands:                        7
% 2.87/1.03  pred_elim:                              2
% 2.87/1.03  pred_elim_cl:                           3
% 2.87/1.03  pred_elim_cycles:                       5
% 2.87/1.03  merged_defs:                            8
% 2.87/1.03  merged_defs_ncl:                        0
% 2.87/1.03  bin_hyper_res:                          8
% 2.87/1.03  prep_cycles:                            4
% 2.87/1.03  pred_elim_time:                         0.006
% 2.87/1.03  splitting_time:                         0.
% 2.87/1.03  sem_filter_time:                        0.
% 2.87/1.03  monotx_time:                            0.001
% 2.87/1.03  subtype_inf_time:                       0.
% 2.87/1.03  
% 2.87/1.03  ------ Problem properties
% 2.87/1.03  
% 2.87/1.03  clauses:                                23
% 2.87/1.03  conjectures:                            4
% 2.87/1.03  epr:                                    5
% 2.87/1.03  horn:                                   13
% 2.87/1.03  ground:                                 4
% 2.87/1.03  unary:                                  5
% 2.87/1.03  binary:                                 8
% 2.87/1.03  lits:                                   70
% 2.87/1.03  lits_eq:                                6
% 2.87/1.03  fd_pure:                                0
% 2.87/1.03  fd_pseudo:                              0
% 2.87/1.03  fd_cond:                                0
% 2.87/1.03  fd_pseudo_cond:                         3
% 2.87/1.03  ac_symbols:                             0
% 2.87/1.03  
% 2.87/1.03  ------ Propositional Solver
% 2.87/1.03  
% 2.87/1.03  prop_solver_calls:                      27
% 2.87/1.03  prop_fast_solver_calls:                 948
% 2.87/1.03  smt_solver_calls:                       0
% 2.87/1.03  smt_fast_solver_calls:                  0
% 2.87/1.03  prop_num_of_clauses:                    2256
% 2.87/1.03  prop_preprocess_simplified:             8474
% 2.87/1.03  prop_fo_subsumed:                       8
% 2.87/1.03  prop_solver_time:                       0.
% 2.87/1.03  smt_solver_time:                        0.
% 2.87/1.03  smt_fast_solver_time:                   0.
% 2.87/1.03  prop_fast_solver_time:                  0.
% 2.87/1.03  prop_unsat_core_time:                   0.
% 2.87/1.03  
% 2.87/1.03  ------ QBF
% 2.87/1.03  
% 2.87/1.03  qbf_q_res:                              0
% 2.87/1.03  qbf_num_tautologies:                    0
% 2.87/1.03  qbf_prep_cycles:                        0
% 2.87/1.03  
% 2.87/1.03  ------ BMC1
% 2.87/1.03  
% 2.87/1.03  bmc1_current_bound:                     -1
% 2.87/1.03  bmc1_last_solved_bound:                 -1
% 2.87/1.03  bmc1_unsat_core_size:                   -1
% 2.87/1.03  bmc1_unsat_core_parents_size:           -1
% 2.87/1.03  bmc1_merge_next_fun:                    0
% 2.87/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.03  
% 2.87/1.03  ------ Instantiation
% 2.87/1.03  
% 2.87/1.03  inst_num_of_clauses:                    651
% 2.87/1.03  inst_num_in_passive:                    408
% 2.87/1.03  inst_num_in_active:                     231
% 2.87/1.03  inst_num_in_unprocessed:                11
% 2.87/1.03  inst_num_of_loops:                      328
% 2.87/1.03  inst_num_of_learning_restarts:          0
% 2.87/1.03  inst_num_moves_active_passive:          93
% 2.87/1.03  inst_lit_activity:                      0
% 2.87/1.03  inst_lit_activity_moves:                0
% 2.87/1.03  inst_num_tautologies:                   0
% 2.87/1.03  inst_num_prop_implied:                  0
% 2.87/1.03  inst_num_existing_simplified:           0
% 2.87/1.03  inst_num_eq_res_simplified:             0
% 2.87/1.03  inst_num_child_elim:                    0
% 2.87/1.03  inst_num_of_dismatching_blockings:      111
% 2.87/1.03  inst_num_of_non_proper_insts:           461
% 2.87/1.03  inst_num_of_duplicates:                 0
% 2.87/1.03  inst_inst_num_from_inst_to_res:         0
% 2.87/1.03  inst_dismatching_checking_time:         0.
% 2.87/1.03  
% 2.87/1.03  ------ Resolution
% 2.87/1.03  
% 2.87/1.03  res_num_of_clauses:                     0
% 2.87/1.03  res_num_in_passive:                     0
% 2.87/1.03  res_num_in_active:                      0
% 2.87/1.03  res_num_of_loops:                       124
% 2.87/1.03  res_forward_subset_subsumed:            21
% 2.87/1.03  res_backward_subset_subsumed:           0
% 2.87/1.03  res_forward_subsumed:                   0
% 2.87/1.03  res_backward_subsumed:                  0
% 2.87/1.03  res_forward_subsumption_resolution:     2
% 2.87/1.03  res_backward_subsumption_resolution:    0
% 2.87/1.03  res_clause_to_clause_subsumption:       724
% 2.87/1.03  res_orphan_elimination:                 0
% 2.87/1.03  res_tautology_del:                      87
% 2.87/1.03  res_num_eq_res_simplified:              0
% 2.87/1.03  res_num_sel_changes:                    0
% 2.87/1.03  res_moves_from_active_to_pass:          0
% 2.87/1.03  
% 2.87/1.03  ------ Superposition
% 2.87/1.03  
% 2.87/1.03  sup_time_total:                         0.
% 2.87/1.03  sup_time_generating:                    0.
% 2.87/1.03  sup_time_sim_full:                      0.
% 2.87/1.03  sup_time_sim_immed:                     0.
% 2.87/1.03  
% 2.87/1.03  sup_num_of_clauses:                     138
% 2.87/1.03  sup_num_in_active:                      60
% 2.87/1.03  sup_num_in_passive:                     78
% 2.87/1.03  sup_num_of_loops:                       64
% 2.87/1.03  sup_fw_superposition:                   88
% 2.87/1.03  sup_bw_superposition:                   139
% 2.87/1.03  sup_immediate_simplified:               39
% 2.87/1.03  sup_given_eliminated:                   2
% 2.87/1.03  comparisons_done:                       0
% 2.87/1.03  comparisons_avoided:                    0
% 2.87/1.03  
% 2.87/1.03  ------ Simplifications
% 2.87/1.03  
% 2.87/1.03  
% 2.87/1.03  sim_fw_subset_subsumed:                 6
% 2.87/1.03  sim_bw_subset_subsumed:                 3
% 2.87/1.03  sim_fw_subsumed:                        22
% 2.87/1.03  sim_bw_subsumed:                        3
% 2.87/1.03  sim_fw_subsumption_res:                 0
% 2.87/1.03  sim_bw_subsumption_res:                 0
% 2.87/1.03  sim_tautology_del:                      16
% 2.87/1.03  sim_eq_tautology_del:                   0
% 2.87/1.03  sim_eq_res_simp:                        3
% 2.87/1.03  sim_fw_demodulated:                     8
% 2.87/1.03  sim_bw_demodulated:                     0
% 2.87/1.03  sim_light_normalised:                   8
% 2.87/1.03  sim_joinable_taut:                      0
% 2.87/1.03  sim_joinable_simp:                      0
% 2.87/1.03  sim_ac_normalised:                      0
% 2.87/1.03  sim_smt_subsumption:                    0
% 2.87/1.03  
%------------------------------------------------------------------------------
