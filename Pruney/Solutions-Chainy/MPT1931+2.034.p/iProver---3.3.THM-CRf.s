%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:13 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 217 expanded)
%              Number of clauses        :   39 (  45 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  407 (1253 expanded)
%              Number of equality atoms :   34 (  93 expanded)
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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f69])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK5,u1_struct_0(X0))
        & l1_waybel_0(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK4,X1,u1_struct_0(sK4))
          & l1_waybel_0(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_waybel_0(sK4,sK5,u1_struct_0(sK4))
    & l1_waybel_0(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_struct_0(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f39,f38])).

fof(f64,plain,(
    ~ r1_waybel_0(sK4,sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f35,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
                      & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f55,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f30])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2002,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),X1)
    | ~ r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),k6_subset_1(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9723,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),X1)
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2002])).

cnf(c_9725,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),k6_subset_1(sK4,sK4))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_9723])).

cnf(c_3203,plain,
    ( ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,sK1(u1_struct_0(sK5)))),X1)
    | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,sK1(u1_struct_0(sK5)))),k6_subset_1(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4751,plain,
    ( ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),X0)
    | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),k6_subset_1(X2,X0)) ),
    inference(instantiation,[status(thm)],[c_3203])).

cnf(c_4753,plain,
    ( ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),k6_subset_1(sK4,sK4))
    | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),sK4) ),
    inference(instantiation,[status(thm)],[c_4751])).

cnf(c_16,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( ~ r1_waybel_0(sK4,sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_319,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k6_subset_1(u1_struct_0(X0),X2) != u1_struct_0(sK4)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_320,plain,
    ( r2_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,negated_conjecture,
    ( l1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_324,plain,
    ( r2_waybel_0(sK4,sK5,X0)
    | k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_22,c_21,c_20,c_19])).

cnf(c_3077,plain,
    ( r2_waybel_0(sK4,sK5,k6_subset_1(X0,X1))
    | k6_subset_1(u1_struct_0(sK4),k6_subset_1(X0,X1)) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_3079,plain,
    ( r2_waybel_0(sK4,sK5,k6_subset_1(sK4,sK4))
    | k6_subset_1(u1_struct_0(sK4),k6_subset_1(sK4,sK4)) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3077])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1079,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),u1_struct_0(sK4))
    | k6_subset_1(u1_struct_0(sK4),X0) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2336,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),u1_struct_0(sK4))
    | k6_subset_1(u1_struct_0(sK4),k6_subset_1(X0,X1)) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_2338,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | k6_subset_1(u1_struct_0(sK4),k6_subset_1(sK4,sK4)) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2336])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1564,plain,
    ( r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),X0)
    | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1570,plain,
    ( ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),k6_subset_1(sK4,sK4))
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),sK4) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_13,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1050,plain,
    ( ~ r2_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,X1)),X0)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1232,plain,
    ( ~ r2_waybel_0(sK4,sK5,X0)
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,sK1(u1_struct_0(sK5)))),X0)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1563,plain,
    ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(X0,X1))
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),k6_subset_1(X0,X1))
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1566,plain,
    ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(sK4,sK4))
    | ~ l1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
    | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),k6_subset_1(sK4,sK4))
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_1332,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1338,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),k6_subset_1(sK4,sK4))
    | r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1089,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),X0)
    | ~ r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),u1_struct_0(sK4))
    | k6_subset_1(u1_struct_0(sK4),X0) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1331,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),k6_subset_1(X0,X1))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),u1_struct_0(sK4))
    | k6_subset_1(u1_struct_0(sK4),k6_subset_1(X0,X1)) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_1334,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),k6_subset_1(sK4,sK4))
    | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
    | k6_subset_1(u1_struct_0(sK4),k6_subset_1(sK4,sK4)) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_6,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1124,plain,
    ( m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9725,c_4753,c_3079,c_2338,c_1570,c_1566,c_1338,c_1334,c_1124,c_19,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.16/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/1.00  
% 3.16/1.00  ------  iProver source info
% 3.16/1.00  
% 3.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/1.00  git: non_committed_changes: false
% 3.16/1.00  git: last_make_outside_of_git: false
% 3.16/1.00  
% 3.16/1.00  ------ 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options
% 3.16/1.00  
% 3.16/1.00  --out_options                           all
% 3.16/1.00  --tptp_safe_out                         true
% 3.16/1.00  --problem_path                          ""
% 3.16/1.00  --include_path                          ""
% 3.16/1.00  --clausifier                            res/vclausify_rel
% 3.16/1.00  --clausifier_options                    --mode clausify
% 3.16/1.00  --stdin                                 false
% 3.16/1.00  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     num_symb
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       true
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  ------ Parsing...
% 3.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/1.00  ------ Proving...
% 3.16/1.00  ------ Problem Properties 
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  clauses                                 19
% 3.16/1.00  conjectures                             4
% 3.16/1.00  EPR                                     4
% 3.16/1.00  Horn                                    11
% 3.16/1.00  unary                                   6
% 3.16/1.00  binary                                  4
% 3.16/1.00  lits                                    60
% 3.16/1.00  lits eq                                 4
% 3.16/1.00  fd_pure                                 0
% 3.16/1.00  fd_pseudo                               0
% 3.16/1.00  fd_cond                                 0
% 3.16/1.00  fd_pseudo_cond                          3
% 3.16/1.00  AC symbols                              0
% 3.16/1.00  
% 3.16/1.00  ------ Schedule dynamic 5 is on 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ 
% 3.16/1.00  Current options:
% 3.16/1.00  ------ 
% 3.16/1.00  
% 3.16/1.00  ------ Input Options
% 3.16/1.00  
% 3.16/1.00  --out_options                           all
% 3.16/1.00  --tptp_safe_out                         true
% 3.16/1.00  --problem_path                          ""
% 3.16/1.00  --include_path                          ""
% 3.16/1.00  --clausifier                            res/vclausify_rel
% 3.16/1.00  --clausifier_options                    --mode clausify
% 3.16/1.00  --stdin                                 false
% 3.16/1.00  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     none
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       false
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ Proving...
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS status Theorem for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  fof(f1,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f25,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.16/1.00    inference(nnf_transformation,[],[f1])).
% 3.16/1.00  
% 3.16/1.00  fof(f26,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.16/1.00    inference(flattening,[],[f25])).
% 3.16/1.00  
% 3.16/1.00  fof(f27,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.16/1.00    inference(rectify,[],[f26])).
% 3.16/1.00  
% 3.16/1.00  fof(f28,plain,(
% 3.16/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f29,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.16/1.00  
% 3.16/1.00  fof(f42,plain,(
% 3.16/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.16/1.00    inference(cnf_transformation,[],[f29])).
% 3.16/1.00  
% 3.16/1.00  fof(f3,axiom,(
% 3.16/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f48,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f3])).
% 3.16/1.00  
% 3.16/1.00  fof(f69,plain,(
% 3.16/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 3.16/1.00    inference(definition_unfolding,[],[f42,f48])).
% 3.16/1.00  
% 3.16/1.00  fof(f72,plain,(
% 3.16/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 3.16/1.00    inference(equality_resolution,[],[f69])).
% 3.16/1.00  
% 3.16/1.00  fof(f9,axiom,(
% 3.16/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f21,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f9])).
% 3.16/1.00  
% 3.16/1.00  fof(f22,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.00    inference(flattening,[],[f21])).
% 3.16/1.00  
% 3.16/1.00  fof(f37,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.00    inference(nnf_transformation,[],[f22])).
% 3.16/1.00  
% 3.16/1.00  fof(f59,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f37])).
% 3.16/1.00  
% 3.16/1.00  fof(f10,conjecture,(
% 3.16/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f11,negated_conjecture,(
% 3.16/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.16/1.00    inference(negated_conjecture,[],[f10])).
% 3.16/1.00  
% 3.16/1.00  fof(f13,plain,(
% 3.16/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.16/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.16/1.00  
% 3.16/1.00  fof(f14,plain,(
% 3.16/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.16/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.16/1.00  
% 3.16/1.00  fof(f23,plain,(
% 3.16/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f14])).
% 3.16/1.00  
% 3.16/1.00  fof(f24,plain,(
% 3.16/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.16/1.00    inference(flattening,[],[f23])).
% 3.16/1.00  
% 3.16/1.00  fof(f39,plain,(
% 3.16/1.00    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK5,u1_struct_0(X0)) & l1_waybel_0(sK5,X0) & ~v2_struct_0(sK5))) )),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f38,plain,(
% 3.16/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK4,X1,u1_struct_0(sK4)) & l1_waybel_0(X1,sK4) & ~v2_struct_0(X1)) & l1_struct_0(sK4) & ~v2_struct_0(sK4))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f40,plain,(
% 3.16/1.00    (~r1_waybel_0(sK4,sK5,u1_struct_0(sK4)) & l1_waybel_0(sK5,sK4) & ~v2_struct_0(sK5)) & l1_struct_0(sK4) & ~v2_struct_0(sK4)),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f39,f38])).
% 3.16/1.00  
% 3.16/1.00  fof(f64,plain,(
% 3.16/1.00    ~r1_waybel_0(sK4,sK5,u1_struct_0(sK4))),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f60,plain,(
% 3.16/1.00    ~v2_struct_0(sK4)),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f61,plain,(
% 3.16/1.00    l1_struct_0(sK4)),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f62,plain,(
% 3.16/1.00    ~v2_struct_0(sK5)),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f63,plain,(
% 3.16/1.00    l1_waybel_0(sK5,sK4)),
% 3.16/1.00    inference(cnf_transformation,[],[f40])).
% 3.16/1.00  
% 3.16/1.00  fof(f44,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f29])).
% 3.16/1.00  
% 3.16/1.00  fof(f67,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/1.00    inference(definition_unfolding,[],[f44,f48])).
% 3.16/1.00  
% 3.16/1.00  fof(f41,plain,(
% 3.16/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.16/1.00    inference(cnf_transformation,[],[f29])).
% 3.16/1.00  
% 3.16/1.00  fof(f70,plain,(
% 3.16/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 3.16/1.00    inference(definition_unfolding,[],[f41,f48])).
% 3.16/1.00  
% 3.16/1.00  fof(f73,plain,(
% 3.16/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 3.16/1.00    inference(equality_resolution,[],[f70])).
% 3.16/1.00  
% 3.16/1.00  fof(f8,axiom,(
% 3.16/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f19,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f8])).
% 3.16/1.00  
% 3.16/1.00  fof(f20,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.00    inference(flattening,[],[f19])).
% 3.16/1.00  
% 3.16/1.00  fof(f32,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.00    inference(nnf_transformation,[],[f20])).
% 3.16/1.00  
% 3.16/1.00  fof(f33,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.00    inference(rectify,[],[f32])).
% 3.16/1.00  
% 3.16/1.00  fof(f35,plain,(
% 3.16/1.00    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f34,plain,(
% 3.16/1.00    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f36,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).
% 3.16/1.00  
% 3.16/1.00  fof(f55,plain,(
% 3.16/1.00    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f36])).
% 3.16/1.00  
% 3.16/1.00  fof(f46,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f29])).
% 3.16/1.00  
% 3.16/1.00  fof(f65,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.16/1.00    inference(definition_unfolding,[],[f46,f48])).
% 3.16/1.00  
% 3.16/1.00  fof(f2,axiom,(
% 3.16/1.00    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f30,plain,(
% 3.16/1.00    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK1(X0),X0))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f31,plain,(
% 3.16/1.00    ! [X0] : m1_subset_1(sK1(X0),X0)),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f30])).
% 3.16/1.00  
% 3.16/1.00  fof(f47,plain,(
% 3.16/1.00    ( ! [X0] : (m1_subset_1(sK1(X0),X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f31])).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2002,plain,
% 3.16/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),X1)
% 3.16/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),k6_subset_1(X2,X1)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_9723,plain,
% 3.16/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),X1)
% 3.16/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),k6_subset_1(X0,X1)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2002]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_9725,plain,
% 3.16/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),k6_subset_1(sK4,sK4))
% 3.16/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_9723]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3203,plain,
% 3.16/1.00      ( ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,sK1(u1_struct_0(sK5)))),X1)
% 3.16/1.00      | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,sK1(u1_struct_0(sK5)))),k6_subset_1(X2,X1)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4751,plain,
% 3.16/1.00      ( ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),X0)
% 3.16/1.00      | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),k6_subset_1(X2,X0)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3203]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4753,plain,
% 3.16/1.00      ( ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),k6_subset_1(sK4,sK4))
% 3.16/1.00      | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_4751]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_16,plain,
% 3.16/1.00      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 3.16/1.00      | r2_waybel_0(X0,X1,X2)
% 3.16/1.00      | ~ l1_waybel_0(X1,X0)
% 3.16/1.00      | ~ l1_struct_0(X0)
% 3.16/1.00      | v2_struct_0(X0)
% 3.16/1.00      | v2_struct_0(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_18,negated_conjecture,
% 3.16/1.00      ( ~ r1_waybel_0(sK4,sK5,u1_struct_0(sK4)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_319,plain,
% 3.16/1.00      ( r2_waybel_0(X0,X1,X2)
% 3.16/1.00      | ~ l1_waybel_0(X1,X0)
% 3.16/1.00      | ~ l1_struct_0(X0)
% 3.16/1.00      | v2_struct_0(X0)
% 3.16/1.00      | v2_struct_0(X1)
% 3.16/1.00      | k6_subset_1(u1_struct_0(X0),X2) != u1_struct_0(sK4)
% 3.16/1.00      | sK5 != X1
% 3.16/1.00      | sK4 != X0 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_320,plain,
% 3.16/1.00      ( r2_waybel_0(sK4,sK5,X0)
% 3.16/1.00      | ~ l1_waybel_0(sK5,sK4)
% 3.16/1.00      | ~ l1_struct_0(sK4)
% 3.16/1.00      | v2_struct_0(sK5)
% 3.16/1.00      | v2_struct_0(sK4)
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_319]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_22,negated_conjecture,
% 3.16/1.00      ( ~ v2_struct_0(sK4) ),
% 3.16/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_21,negated_conjecture,
% 3.16/1.00      ( l1_struct_0(sK4) ),
% 3.16/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_20,negated_conjecture,
% 3.16/1.00      ( ~ v2_struct_0(sK5) ),
% 3.16/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_19,negated_conjecture,
% 3.16/1.00      ( l1_waybel_0(sK5,sK4) ),
% 3.16/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_324,plain,
% 3.16/1.00      ( r2_waybel_0(sK4,sK5,X0)
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),X0) != u1_struct_0(sK4) ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_320,c_22,c_21,c_20,c_19]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3077,plain,
% 3.16/1.00      ( r2_waybel_0(sK4,sK5,k6_subset_1(X0,X1))
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),k6_subset_1(X0,X1)) != u1_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_324]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3079,plain,
% 3.16/1.00      ( r2_waybel_0(sK4,sK5,k6_subset_1(sK4,sK4))
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),k6_subset_1(sK4,sK4)) != u1_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3077]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2,plain,
% 3.16/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.16/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.16/1.00      | k6_subset_1(X0,X1) = X2 ),
% 3.16/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1079,plain,
% 3.16/1.00      ( r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),X0) = u1_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2336,plain,
% 3.16/1.00      ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),k6_subset_1(X0,X1)) = u1_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1079]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2338,plain,
% 3.16/1.00      ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),k6_subset_1(sK4,sK4)) = u1_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2336]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5,plain,
% 3.16/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1564,plain,
% 3.16/1.00      ( r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),X0)
% 3.16/1.00      | ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),k6_subset_1(X0,X1)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1570,plain,
% 3.16/1.00      ( ~ r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),k6_subset_1(sK4,sK4))
% 3.16/1.00      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1564]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_13,plain,
% 3.16/1.00      ( ~ r2_waybel_0(X0,X1,X2)
% 3.16/1.00      | ~ l1_waybel_0(X1,X0)
% 3.16/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.16/1.00      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
% 3.16/1.00      | ~ l1_struct_0(X0)
% 3.16/1.00      | v2_struct_0(X0)
% 3.16/1.00      | v2_struct_0(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1050,plain,
% 3.16/1.00      ( ~ r2_waybel_0(sK4,sK5,X0)
% 3.16/1.00      | ~ l1_waybel_0(sK5,sK4)
% 3.16/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.16/1.00      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,X1)),X0)
% 3.16/1.00      | ~ l1_struct_0(sK4)
% 3.16/1.00      | v2_struct_0(sK5)
% 3.16/1.00      | v2_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1232,plain,
% 3.16/1.00      ( ~ r2_waybel_0(sK4,sK5,X0)
% 3.16/1.00      | ~ l1_waybel_0(sK5,sK4)
% 3.16/1.00      | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
% 3.16/1.00      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,X0,sK1(u1_struct_0(sK5)))),X0)
% 3.16/1.00      | ~ l1_struct_0(sK4)
% 3.16/1.00      | v2_struct_0(sK5)
% 3.16/1.00      | v2_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1050]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1563,plain,
% 3.16/1.00      ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(X0,X1))
% 3.16/1.00      | ~ l1_waybel_0(sK5,sK4)
% 3.16/1.00      | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
% 3.16/1.00      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(X0,X1),sK1(u1_struct_0(sK5)))),k6_subset_1(X0,X1))
% 3.16/1.00      | ~ l1_struct_0(sK4)
% 3.16/1.00      | v2_struct_0(sK5)
% 3.16/1.00      | v2_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1232]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1566,plain,
% 3.16/1.00      ( ~ r2_waybel_0(sK4,sK5,k6_subset_1(sK4,sK4))
% 3.16/1.00      | ~ l1_waybel_0(sK5,sK4)
% 3.16/1.00      | ~ m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5))
% 3.16/1.00      | r2_hidden(k2_waybel_0(sK4,sK5,sK3(sK4,sK5,k6_subset_1(sK4,sK4),sK1(u1_struct_0(sK5)))),k6_subset_1(sK4,sK4))
% 3.16/1.00      | ~ l1_struct_0(sK4)
% 3.16/1.00      | v2_struct_0(sK5)
% 3.16/1.00      | v2_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1563]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1332,plain,
% 3.16/1.00      ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),X0)
% 3.16/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),k6_subset_1(X0,X1)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1338,plain,
% 3.16/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),k6_subset_1(sK4,sK4))
% 3.16/1.00      | r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1332]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_0,plain,
% 3.16/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.16/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.16/1.00      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.16/1.00      | k6_subset_1(X0,X1) = X2 ),
% 3.16/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1089,plain,
% 3.16/1.00      ( r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),X0)
% 3.16/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK4),X0,u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),X0) = u1_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1331,plain,
% 3.16/1.00      ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),k6_subset_1(X0,X1))
% 3.16/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(X0,X1),u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),k6_subset_1(X0,X1)) = u1_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1089]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1334,plain,
% 3.16/1.00      ( r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),k6_subset_1(sK4,sK4))
% 3.16/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK4),k6_subset_1(sK4,sK4),u1_struct_0(sK4)),u1_struct_0(sK4))
% 3.16/1.00      | k6_subset_1(u1_struct_0(sK4),k6_subset_1(sK4,sK4)) = u1_struct_0(sK4) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_1331]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6,plain,
% 3.16/1.00      ( m1_subset_1(sK1(X0),X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_1124,plain,
% 3.16/1.00      ( m1_subset_1(sK1(u1_struct_0(sK5)),u1_struct_0(sK5)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(contradiction,plain,
% 3.16/1.00      ( $false ),
% 3.16/1.00      inference(minisat,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_9725,c_4753,c_3079,c_2338,c_1570,c_1566,c_1338,c_1334,
% 3.16/1.00                 c_1124,c_19,c_20,c_21,c_22]) ).
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  ------                               Statistics
% 3.16/1.00  
% 3.16/1.00  ------ General
% 3.16/1.00  
% 3.16/1.00  abstr_ref_over_cycles:                  0
% 3.16/1.00  abstr_ref_under_cycles:                 0
% 3.16/1.00  gc_basic_clause_elim:                   0
% 3.16/1.00  forced_gc_time:                         0
% 3.16/1.00  parsing_time:                           0.008
% 3.16/1.00  unif_index_cands_time:                  0.
% 3.16/1.00  unif_index_add_time:                    0.
% 3.16/1.00  orderings_time:                         0.
% 3.16/1.00  out_proof_time:                         0.007
% 3.16/1.00  total_time:                             0.305
% 3.16/1.00  num_of_symbols:                         51
% 3.16/1.00  num_of_terms:                           10765
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing
% 3.16/1.00  
% 3.16/1.00  num_of_splits:                          0
% 3.16/1.00  num_of_split_atoms:                     0
% 3.16/1.00  num_of_reused_defs:                     0
% 3.16/1.00  num_eq_ax_congr_red:                    51
% 3.16/1.00  num_of_sem_filtered_clauses:            1
% 3.16/1.00  num_of_subtypes:                        0
% 3.16/1.00  monotx_restored_types:                  0
% 3.16/1.00  sat_num_of_epr_types:                   0
% 3.16/1.00  sat_num_of_non_cyclic_types:            0
% 3.16/1.00  sat_guarded_non_collapsed_types:        0
% 3.16/1.00  num_pure_diseq_elim:                    0
% 3.16/1.00  simp_replaced_by:                       0
% 3.16/1.00  res_preprocessed:                       105
% 3.16/1.00  prep_upred:                             0
% 3.16/1.00  prep_unflattend:                        5
% 3.16/1.00  smt_new_axioms:                         0
% 3.16/1.00  pred_elim_cands:                        6
% 3.16/1.00  pred_elim:                              3
% 3.16/1.00  pred_elim_cl:                           4
% 3.16/1.00  pred_elim_cycles:                       5
% 3.16/1.00  merged_defs:                            0
% 3.16/1.00  merged_defs_ncl:                        0
% 3.16/1.00  bin_hyper_res:                          0
% 3.16/1.00  prep_cycles:                            4
% 3.16/1.00  pred_elim_time:                         0.003
% 3.16/1.00  splitting_time:                         0.
% 3.16/1.00  sem_filter_time:                        0.
% 3.16/1.00  monotx_time:                            0.001
% 3.16/1.00  subtype_inf_time:                       0.
% 3.16/1.00  
% 3.16/1.00  ------ Problem properties
% 3.16/1.00  
% 3.16/1.00  clauses:                                19
% 3.16/1.00  conjectures:                            4
% 3.16/1.00  epr:                                    4
% 3.16/1.00  horn:                                   11
% 3.16/1.00  ground:                                 4
% 3.16/1.00  unary:                                  6
% 3.16/1.00  binary:                                 4
% 3.16/1.00  lits:                                   60
% 3.16/1.00  lits_eq:                                4
% 3.16/1.00  fd_pure:                                0
% 3.16/1.00  fd_pseudo:                              0
% 3.16/1.00  fd_cond:                                0
% 3.16/1.00  fd_pseudo_cond:                         3
% 3.16/1.00  ac_symbols:                             0
% 3.16/1.00  
% 3.16/1.00  ------ Propositional Solver
% 3.16/1.00  
% 3.16/1.00  prop_solver_calls:                      28
% 3.16/1.00  prop_fast_solver_calls:                 858
% 3.16/1.00  smt_solver_calls:                       0
% 3.16/1.00  smt_fast_solver_calls:                  0
% 3.16/1.00  prop_num_of_clauses:                    2501
% 3.16/1.00  prop_preprocess_simplified:             6800
% 3.16/1.00  prop_fo_subsumed:                       5
% 3.16/1.00  prop_solver_time:                       0.
% 3.16/1.00  smt_solver_time:                        0.
% 3.16/1.00  smt_fast_solver_time:                   0.
% 3.16/1.00  prop_fast_solver_time:                  0.
% 3.16/1.00  prop_unsat_core_time:                   0.
% 3.16/1.00  
% 3.16/1.00  ------ QBF
% 3.16/1.00  
% 3.16/1.00  qbf_q_res:                              0
% 3.16/1.00  qbf_num_tautologies:                    0
% 3.16/1.00  qbf_prep_cycles:                        0
% 3.16/1.00  
% 3.16/1.00  ------ BMC1
% 3.16/1.00  
% 3.16/1.00  bmc1_current_bound:                     -1
% 3.16/1.00  bmc1_last_solved_bound:                 -1
% 3.16/1.00  bmc1_unsat_core_size:                   -1
% 3.16/1.00  bmc1_unsat_core_parents_size:           -1
% 3.16/1.00  bmc1_merge_next_fun:                    0
% 3.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation
% 3.16/1.00  
% 3.16/1.00  inst_num_of_clauses:                    602
% 3.16/1.00  inst_num_in_passive:                    286
% 3.16/1.00  inst_num_in_active:                     294
% 3.16/1.00  inst_num_in_unprocessed:                21
% 3.16/1.00  inst_num_of_loops:                      386
% 3.16/1.00  inst_num_of_learning_restarts:          0
% 3.16/1.00  inst_num_moves_active_passive:          88
% 3.16/1.00  inst_lit_activity:                      0
% 3.16/1.00  inst_lit_activity_moves:                0
% 3.16/1.00  inst_num_tautologies:                   0
% 3.16/1.00  inst_num_prop_implied:                  0
% 3.16/1.00  inst_num_existing_simplified:           0
% 3.16/1.00  inst_num_eq_res_simplified:             0
% 3.16/1.00  inst_num_child_elim:                    0
% 3.16/1.00  inst_num_of_dismatching_blockings:      233
% 3.16/1.00  inst_num_of_non_proper_insts:           552
% 3.16/1.00  inst_num_of_duplicates:                 0
% 3.16/1.00  inst_inst_num_from_inst_to_res:         0
% 3.16/1.00  inst_dismatching_checking_time:         0.
% 3.16/1.00  
% 3.16/1.00  ------ Resolution
% 3.16/1.00  
% 3.16/1.00  res_num_of_clauses:                     0
% 3.16/1.00  res_num_in_passive:                     0
% 3.16/1.00  res_num_in_active:                      0
% 3.16/1.00  res_num_of_loops:                       109
% 3.16/1.00  res_forward_subset_subsumed:            34
% 3.16/1.00  res_backward_subset_subsumed:           0
% 3.16/1.00  res_forward_subsumed:                   0
% 3.16/1.00  res_backward_subsumed:                  0
% 3.16/1.00  res_forward_subsumption_resolution:     2
% 3.16/1.00  res_backward_subsumption_resolution:    0
% 3.16/1.00  res_clause_to_clause_subsumption:       3538
% 3.16/1.00  res_orphan_elimination:                 0
% 3.16/1.00  res_tautology_del:                      71
% 3.16/1.00  res_num_eq_res_simplified:              0
% 3.16/1.00  res_num_sel_changes:                    0
% 3.16/1.00  res_moves_from_active_to_pass:          0
% 3.16/1.00  
% 3.16/1.00  ------ Superposition
% 3.16/1.00  
% 3.16/1.00  sup_time_total:                         0.
% 3.16/1.00  sup_time_generating:                    0.
% 3.16/1.00  sup_time_sim_full:                      0.
% 3.16/1.00  sup_time_sim_immed:                     0.
% 3.16/1.00  
% 3.16/1.00  sup_num_of_clauses:                     265
% 3.16/1.00  sup_num_in_active:                      75
% 3.16/1.00  sup_num_in_passive:                     190
% 3.16/1.00  sup_num_of_loops:                       76
% 3.16/1.00  sup_fw_superposition:                   851
% 3.16/1.00  sup_bw_superposition:                   689
% 3.16/1.00  sup_immediate_simplified:               822
% 3.16/1.00  sup_given_eliminated:                   1
% 3.16/1.00  comparisons_done:                       0
% 3.16/1.00  comparisons_avoided:                    0
% 3.16/1.00  
% 3.16/1.00  ------ Simplifications
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  sim_fw_subset_subsumed:                 38
% 3.16/1.00  sim_bw_subset_subsumed:                 1
% 3.16/1.00  sim_fw_subsumed:                        220
% 3.16/1.00  sim_bw_subsumed:                        3
% 3.16/1.00  sim_fw_subsumption_res:                 4
% 3.16/1.00  sim_bw_subsumption_res:                 0
% 3.16/1.00  sim_tautology_del:                      33
% 3.16/1.00  sim_eq_tautology_del:                   124
% 3.16/1.00  sim_eq_res_simp:                        1
% 3.16/1.00  sim_fw_demodulated:                     323
% 3.16/1.00  sim_bw_demodulated:                     2
% 3.16/1.00  sim_light_normalised:                   300
% 3.16/1.00  sim_joinable_taut:                      0
% 3.16/1.00  sim_joinable_simp:                      0
% 3.16/1.00  sim_ac_normalised:                      0
% 3.16/1.00  sim_smt_subsumption:                    0
% 3.16/1.00  
%------------------------------------------------------------------------------
