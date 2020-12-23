%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:09 EST 2020

% Result     : Theorem 7.45s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 228 expanded)
%              Number of clauses        :   45 (  53 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  521 (1195 expanded)
%              Number of equality atoms :   60 (  95 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK6,u1_struct_0(X0))
        & l1_waybel_0(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK5,X1,u1_struct_0(sK5))
          & l1_waybel_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5))
    & l1_waybel_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f47,f46])).

fof(f75,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5))
        & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5))
                      & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f41,f43,f42])).

fof(f68,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f64])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f84])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5403,plain,
    ( r2_hidden(sK2(X0,X1,X2),X2)
    | ~ v1_xboole_0(X0)
    | k6_subset_1(X0,X1) = X2 ),
    inference(resolution,[status(thm)],[c_6,c_1])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2189,plain,
    ( r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2526,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1967,plain,
    ( m1_subset_1(X0,u1_struct_0(sK6))
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2623,plain,
    ( m1_subset_1(u1_struct_0(sK6),u1_struct_0(sK6))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_18,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1701,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,X1)),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3356,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK0(u1_struct_0(sK6)),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK0(u1_struct_0(sK6)))),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_1730,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,X1)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4032,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK0(u1_struct_0(sK6)))),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_4874,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(u1_struct_0(sK6),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,u1_struct_0(sK6))),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_6871,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,u1_struct_0(sK6))),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1385,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1379,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k6_subset_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1785,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top
    | r2_hidden(sK1(k6_subset_1(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1385,c_1379])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1386,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4175,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1386])).

cnf(c_21,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1370,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) = iProver_top
    | r2_waybel_0(X0,X1,X2) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_tarski(X2,X3)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1367,plain,
    ( r1_waybel_0(X0,X1,X2) != iProver_top
    | r1_waybel_0(X0,X1,X3) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2552,plain,
    ( r1_waybel_0(X0,X1,X2) = iProver_top
    | r2_waybel_0(X0,X1,X3) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | r1_tarski(k6_subset_1(u1_struct_0(X0),X3),X2) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_1367])).

cnf(c_4194,plain,
    ( r1_waybel_0(X0,X1,u1_struct_0(X0)) = iProver_top
    | r2_waybel_0(X0,X1,X2) = iProver_top
    | l1_waybel_0(X1,X0) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4175,c_2552])).

cnf(c_25,negated_conjecture,
    ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1366,plain,
    ( r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9259,plain,
    ( r2_waybel_0(sK5,sK6,X0) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4194,c_1366])).

cnf(c_9273,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9259])).

cnf(c_9388,plain,
    ( ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5403,c_29,c_28,c_27,c_26,c_2189,c_2526,c_2623,c_3356,c_4032,c_4874,c_6871,c_9273])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2846,plain,
    ( ~ r2_hidden(sK0(k6_subset_1(X0,X1)),X1)
    | v1_xboole_0(k6_subset_1(X0,X1)) ),
    inference(resolution,[status(thm)],[c_8,c_0])).

cnf(c_2458,plain,
    ( r2_hidden(sK0(k6_subset_1(X0,X1)),X0)
    | v1_xboole_0(k6_subset_1(X0,X1)) ),
    inference(resolution,[status(thm)],[c_9,c_0])).

cnf(c_2908,plain,
    ( v1_xboole_0(k6_subset_1(X0,X0)) ),
    inference(resolution,[status(thm)],[c_2846,c_2458])).

cnf(c_23438,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_9388,c_2908])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.45/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/1.50  
% 7.45/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.45/1.50  
% 7.45/1.50  ------  iProver source info
% 7.45/1.50  
% 7.45/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.45/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.45/1.50  git: non_committed_changes: false
% 7.45/1.50  git: last_make_outside_of_git: false
% 7.45/1.50  
% 7.45/1.50  ------ 
% 7.45/1.50  ------ Parsing...
% 7.45/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.45/1.50  
% 7.45/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.45/1.50  
% 7.45/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.45/1.50  
% 7.45/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.45/1.50  ------ Proving...
% 7.45/1.50  ------ Problem Properties 
% 7.45/1.50  
% 7.45/1.50  
% 7.45/1.50  clauses                                 28
% 7.45/1.50  conjectures                             5
% 7.45/1.50  EPR                                     11
% 7.45/1.50  Horn                                    13
% 7.45/1.50  unary                                   5
% 7.45/1.50  binary                                  7
% 7.45/1.50  lits                                    100
% 7.45/1.50  lits eq                                 3
% 7.45/1.50  fd_pure                                 0
% 7.45/1.50  fd_pseudo                               0
% 7.45/1.50  fd_cond                                 0
% 7.45/1.50  fd_pseudo_cond                          3
% 7.45/1.50  AC symbols                              0
% 7.45/1.50  
% 7.45/1.50  ------ Input Options Time Limit: Unbounded
% 7.45/1.50  
% 7.45/1.50  
% 7.45/1.50  ------ 
% 7.45/1.50  Current options:
% 7.45/1.50  ------ 
% 7.45/1.50  
% 7.45/1.50  
% 7.45/1.50  
% 7.45/1.50  
% 7.45/1.50  ------ Proving...
% 7.45/1.50  
% 7.45/1.50  
% 7.45/1.50  % SZS status Theorem for theBenchmark.p
% 7.45/1.50  
% 7.45/1.50   Resolution empty clause
% 7.45/1.50  
% 7.45/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.45/1.50  
% 7.45/1.50  fof(f3,axiom,(
% 7.45/1.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f34,plain,(
% 7.45/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.45/1.50    inference(nnf_transformation,[],[f3])).
% 7.45/1.50  
% 7.45/1.50  fof(f35,plain,(
% 7.45/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.45/1.50    inference(flattening,[],[f34])).
% 7.45/1.50  
% 7.45/1.50  fof(f36,plain,(
% 7.45/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.45/1.50    inference(rectify,[],[f35])).
% 7.45/1.50  
% 7.45/1.50  fof(f37,plain,(
% 7.45/1.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.45/1.50    introduced(choice_axiom,[])).
% 7.45/1.50  
% 7.45/1.50  fof(f38,plain,(
% 7.45/1.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.45/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 7.45/1.50  
% 7.45/1.50  fof(f56,plain,(
% 7.45/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f38])).
% 7.45/1.50  
% 7.45/1.50  fof(f6,axiom,(
% 7.45/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f64,plain,(
% 7.45/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f6])).
% 7.45/1.50  
% 7.45/1.50  fof(f82,plain,(
% 7.45/1.50    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 7.45/1.50    inference(definition_unfolding,[],[f56,f64])).
% 7.45/1.50  
% 7.45/1.50  fof(f1,axiom,(
% 7.45/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f28,plain,(
% 7.45/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.50    inference(nnf_transformation,[],[f1])).
% 7.45/1.50  
% 7.45/1.50  fof(f29,plain,(
% 7.45/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.50    inference(rectify,[],[f28])).
% 7.45/1.50  
% 7.45/1.50  fof(f30,plain,(
% 7.45/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.45/1.50    introduced(choice_axiom,[])).
% 7.45/1.50  
% 7.45/1.50  fof(f31,plain,(
% 7.45/1.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.45/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.45/1.50  
% 7.45/1.50  fof(f49,plain,(
% 7.45/1.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f31])).
% 7.45/1.50  
% 7.45/1.50  fof(f11,conjecture,(
% 7.45/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f12,negated_conjecture,(
% 7.45/1.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 7.45/1.50    inference(negated_conjecture,[],[f11])).
% 7.45/1.50  
% 7.45/1.50  fof(f14,plain,(
% 7.45/1.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 7.45/1.50    inference(pure_predicate_removal,[],[f12])).
% 7.45/1.50  
% 7.45/1.50  fof(f15,plain,(
% 7.45/1.50    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 7.45/1.50    inference(pure_predicate_removal,[],[f14])).
% 7.45/1.50  
% 7.45/1.50  fof(f26,plain,(
% 7.45/1.50    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 7.45/1.50    inference(ennf_transformation,[],[f15])).
% 7.45/1.50  
% 7.45/1.50  fof(f27,plain,(
% 7.45/1.50    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 7.45/1.50    inference(flattening,[],[f26])).
% 7.45/1.50  
% 7.45/1.50  fof(f47,plain,(
% 7.45/1.50    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK6,u1_struct_0(X0)) & l1_waybel_0(sK6,X0) & ~v2_struct_0(sK6))) )),
% 7.45/1.50    introduced(choice_axiom,[])).
% 7.45/1.50  
% 7.45/1.50  fof(f46,plain,(
% 7.45/1.50    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK5,X1,u1_struct_0(sK5)) & l1_waybel_0(X1,sK5) & ~v2_struct_0(X1)) & l1_struct_0(sK5) & ~v2_struct_0(sK5))),
% 7.45/1.50    introduced(choice_axiom,[])).
% 7.45/1.50  
% 7.45/1.50  fof(f48,plain,(
% 7.45/1.50    (~r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) & l1_waybel_0(sK6,sK5) & ~v2_struct_0(sK6)) & l1_struct_0(sK5) & ~v2_struct_0(sK5)),
% 7.45/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f47,f46])).
% 7.45/1.50  
% 7.45/1.50  fof(f75,plain,(
% 7.45/1.50    ~v2_struct_0(sK5)),
% 7.45/1.50    inference(cnf_transformation,[],[f48])).
% 7.45/1.50  
% 7.45/1.50  fof(f76,plain,(
% 7.45/1.50    l1_struct_0(sK5)),
% 7.45/1.50    inference(cnf_transformation,[],[f48])).
% 7.45/1.50  
% 7.45/1.50  fof(f77,plain,(
% 7.45/1.50    ~v2_struct_0(sK6)),
% 7.45/1.50    inference(cnf_transformation,[],[f48])).
% 7.45/1.50  
% 7.45/1.50  fof(f78,plain,(
% 7.45/1.50    l1_waybel_0(sK6,sK5)),
% 7.45/1.50    inference(cnf_transformation,[],[f48])).
% 7.45/1.50  
% 7.45/1.50  fof(f50,plain,(
% 7.45/1.50    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f31])).
% 7.45/1.50  
% 7.45/1.50  fof(f7,axiom,(
% 7.45/1.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f19,plain,(
% 7.45/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.45/1.50    inference(ennf_transformation,[],[f7])).
% 7.45/1.50  
% 7.45/1.50  fof(f65,plain,(
% 7.45/1.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f19])).
% 7.45/1.50  
% 7.45/1.50  fof(f4,axiom,(
% 7.45/1.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f17,plain,(
% 7.45/1.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.45/1.50    inference(ennf_transformation,[],[f4])).
% 7.45/1.50  
% 7.45/1.50  fof(f39,plain,(
% 7.45/1.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.45/1.50    inference(nnf_transformation,[],[f17])).
% 7.45/1.50  
% 7.45/1.50  fof(f62,plain,(
% 7.45/1.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f39])).
% 7.45/1.50  
% 7.45/1.50  fof(f8,axiom,(
% 7.45/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f20,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.45/1.50    inference(ennf_transformation,[],[f8])).
% 7.45/1.50  
% 7.45/1.50  fof(f21,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.45/1.50    inference(flattening,[],[f20])).
% 7.45/1.50  
% 7.45/1.50  fof(f40,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.45/1.50    inference(nnf_transformation,[],[f21])).
% 7.45/1.50  
% 7.45/1.50  fof(f41,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.45/1.50    inference(rectify,[],[f40])).
% 7.45/1.50  
% 7.45/1.50  fof(f43,plain,(
% 7.45/1.50    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5)) & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1))))),
% 7.45/1.50    introduced(choice_axiom,[])).
% 7.45/1.50  
% 7.45/1.50  fof(f42,plain,(
% 7.45/1.50    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 7.45/1.50    introduced(choice_axiom,[])).
% 7.45/1.50  
% 7.45/1.50  fof(f44,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5)) & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.45/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f41,f43,f42])).
% 7.45/1.50  
% 7.45/1.50  fof(f68,plain,(
% 7.45/1.50    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f44])).
% 7.45/1.50  
% 7.45/1.50  fof(f2,axiom,(
% 7.45/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f13,plain,(
% 7.45/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.45/1.50    inference(unused_predicate_definition_removal,[],[f2])).
% 7.45/1.50  
% 7.45/1.50  fof(f16,plain,(
% 7.45/1.50    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.45/1.50    inference(ennf_transformation,[],[f13])).
% 7.45/1.50  
% 7.45/1.50  fof(f32,plain,(
% 7.45/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.45/1.50    introduced(choice_axiom,[])).
% 7.45/1.50  
% 7.45/1.50  fof(f33,plain,(
% 7.45/1.50    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.45/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f32])).
% 7.45/1.50  
% 7.45/1.50  fof(f51,plain,(
% 7.45/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f33])).
% 7.45/1.50  
% 7.45/1.50  fof(f53,plain,(
% 7.45/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.45/1.50    inference(cnf_transformation,[],[f38])).
% 7.45/1.50  
% 7.45/1.50  fof(f85,plain,(
% 7.45/1.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 7.45/1.50    inference(definition_unfolding,[],[f53,f64])).
% 7.45/1.50  
% 7.45/1.50  fof(f88,plain,(
% 7.45/1.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 7.45/1.50    inference(equality_resolution,[],[f85])).
% 7.45/1.50  
% 7.45/1.50  fof(f52,plain,(
% 7.45/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f33])).
% 7.45/1.50  
% 7.45/1.50  fof(f9,axiom,(
% 7.45/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f22,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.45/1.50    inference(ennf_transformation,[],[f9])).
% 7.45/1.50  
% 7.45/1.50  fof(f23,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.45/1.50    inference(flattening,[],[f22])).
% 7.45/1.50  
% 7.45/1.50  fof(f45,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.45/1.50    inference(nnf_transformation,[],[f23])).
% 7.45/1.50  
% 7.45/1.50  fof(f72,plain,(
% 7.45/1.50    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f45])).
% 7.45/1.50  
% 7.45/1.50  fof(f10,axiom,(
% 7.45/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 7.45/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.45/1.50  
% 7.45/1.50  fof(f24,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.45/1.50    inference(ennf_transformation,[],[f10])).
% 7.45/1.50  
% 7.45/1.50  fof(f25,plain,(
% 7.45/1.50    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.45/1.50    inference(flattening,[],[f24])).
% 7.45/1.50  
% 7.45/1.50  fof(f73,plain,(
% 7.45/1.50    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2) | ~r1_tarski(X2,X3) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.45/1.50    inference(cnf_transformation,[],[f25])).
% 7.45/1.50  
% 7.45/1.50  fof(f79,plain,(
% 7.45/1.50    ~r1_waybel_0(sK5,sK6,u1_struct_0(sK5))),
% 7.45/1.50    inference(cnf_transformation,[],[f48])).
% 7.45/1.50  
% 7.45/1.50  fof(f54,plain,(
% 7.45/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.45/1.50    inference(cnf_transformation,[],[f38])).
% 7.45/1.50  
% 7.45/1.50  fof(f84,plain,(
% 7.45/1.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 7.45/1.50    inference(definition_unfolding,[],[f54,f64])).
% 7.45/1.50  
% 7.45/1.50  fof(f87,plain,(
% 7.45/1.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 7.45/1.50    inference(equality_resolution,[],[f84])).
% 7.45/1.50  
% 7.45/1.50  cnf(c_6,plain,
% 7.45/1.50      ( r2_hidden(sK2(X0,X1,X2),X0)
% 7.45/1.50      | r2_hidden(sK2(X0,X1,X2),X2)
% 7.45/1.50      | k6_subset_1(X0,X1) = X2 ),
% 7.45/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1,plain,
% 7.45/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.45/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_5403,plain,
% 7.45/1.50      ( r2_hidden(sK2(X0,X1,X2),X2)
% 7.45/1.50      | ~ v1_xboole_0(X0)
% 7.45/1.50      | k6_subset_1(X0,X1) = X2 ),
% 7.45/1.50      inference(resolution,[status(thm)],[c_6,c_1]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_29,negated_conjecture,
% 7.45/1.50      ( ~ v2_struct_0(sK5) ),
% 7.45/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_28,negated_conjecture,
% 7.45/1.50      ( l1_struct_0(sK5) ),
% 7.45/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_27,negated_conjecture,
% 7.45/1.50      ( ~ v2_struct_0(sK6) ),
% 7.45/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_26,negated_conjecture,
% 7.45/1.50      ( l1_waybel_0(sK6,sK5) ),
% 7.45/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_0,plain,
% 7.45/1.50      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 7.45/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_2189,plain,
% 7.45/1.50      ( r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.45/1.50      | v1_xboole_0(u1_struct_0(sK6)) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_15,plain,
% 7.45/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.45/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_2526,plain,
% 7.45/1.50      ( m1_subset_1(sK0(u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.45/1.50      | ~ r2_hidden(sK0(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_10,plain,
% 7.45/1.50      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 7.45/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1967,plain,
% 7.45/1.50      ( m1_subset_1(X0,u1_struct_0(sK6))
% 7.45/1.50      | ~ v1_xboole_0(X0)
% 7.45/1.50      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_2623,plain,
% 7.45/1.50      ( m1_subset_1(u1_struct_0(sK6),u1_struct_0(sK6))
% 7.45/1.50      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_1967]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_18,plain,
% 7.45/1.50      ( ~ r2_waybel_0(X0,X1,X2)
% 7.45/1.50      | ~ l1_waybel_0(X1,X0)
% 7.45/1.50      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 7.45/1.50      | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
% 7.45/1.50      | ~ l1_struct_0(X0)
% 7.45/1.50      | v2_struct_0(X0)
% 7.45/1.50      | v2_struct_0(X1) ),
% 7.45/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1701,plain,
% 7.45/1.50      ( ~ r2_waybel_0(sK5,sK6,X0)
% 7.45/1.50      | ~ l1_waybel_0(sK6,sK5)
% 7.45/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 7.45/1.50      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,X1)),X0)
% 7.45/1.50      | ~ l1_struct_0(sK5)
% 7.45/1.50      | v2_struct_0(sK6)
% 7.45/1.50      | v2_struct_0(sK5) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_3356,plain,
% 7.45/1.50      ( ~ r2_waybel_0(sK5,sK6,X0)
% 7.45/1.50      | ~ l1_waybel_0(sK6,sK5)
% 7.45/1.50      | ~ m1_subset_1(sK0(u1_struct_0(sK6)),u1_struct_0(sK6))
% 7.45/1.50      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK0(u1_struct_0(sK6)))),X0)
% 7.45/1.50      | ~ l1_struct_0(sK5)
% 7.45/1.50      | v2_struct_0(sK6)
% 7.45/1.50      | v2_struct_0(sK5) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_1701]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1730,plain,
% 7.45/1.50      ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,X1)),X0)
% 7.45/1.50      | ~ v1_xboole_0(X0) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_4032,plain,
% 7.45/1.50      ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK0(u1_struct_0(sK6)))),X0)
% 7.45/1.50      | ~ v1_xboole_0(X0) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_1730]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_4874,plain,
% 7.45/1.50      ( ~ r2_waybel_0(sK5,sK6,X0)
% 7.45/1.50      | ~ l1_waybel_0(sK6,sK5)
% 7.45/1.50      | ~ m1_subset_1(u1_struct_0(sK6),u1_struct_0(sK6))
% 7.45/1.50      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,u1_struct_0(sK6))),X0)
% 7.45/1.50      | ~ l1_struct_0(sK5)
% 7.45/1.50      | v2_struct_0(sK6)
% 7.45/1.50      | v2_struct_0(sK5) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_1701]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_6871,plain,
% 7.45/1.50      ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,u1_struct_0(sK6))),X0)
% 7.45/1.50      | ~ v1_xboole_0(X0) ),
% 7.45/1.50      inference(instantiation,[status(thm)],[c_1730]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_3,plain,
% 7.45/1.50      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.45/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1385,plain,
% 7.45/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.45/1.50      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.45/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_9,plain,
% 7.45/1.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 7.45/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1379,plain,
% 7.45/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.45/1.50      | r2_hidden(X0,k6_subset_1(X1,X2)) != iProver_top ),
% 7.45/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1785,plain,
% 7.45/1.50      ( r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top
% 7.45/1.50      | r2_hidden(sK1(k6_subset_1(X0,X1),X2),X0) = iProver_top ),
% 7.45/1.50      inference(superposition,[status(thm)],[c_1385,c_1379]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_2,plain,
% 7.45/1.50      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 7.45/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1386,plain,
% 7.45/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.45/1.50      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 7.45/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_4175,plain,
% 7.45/1.50      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 7.45/1.50      inference(superposition,[status(thm)],[c_1785,c_1386]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_21,plain,
% 7.45/1.50      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 7.45/1.50      | r2_waybel_0(X0,X1,X2)
% 7.45/1.50      | ~ l1_waybel_0(X1,X0)
% 7.45/1.50      | ~ l1_struct_0(X0)
% 7.45/1.50      | v2_struct_0(X0)
% 7.45/1.50      | v2_struct_0(X1) ),
% 7.45/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1370,plain,
% 7.45/1.50      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) = iProver_top
% 7.45/1.50      | r2_waybel_0(X0,X1,X2) = iProver_top
% 7.45/1.50      | l1_waybel_0(X1,X0) != iProver_top
% 7.45/1.50      | l1_struct_0(X0) != iProver_top
% 7.45/1.50      | v2_struct_0(X0) = iProver_top
% 7.45/1.50      | v2_struct_0(X1) = iProver_top ),
% 7.45/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_24,plain,
% 7.45/1.50      ( ~ r1_waybel_0(X0,X1,X2)
% 7.45/1.50      | r1_waybel_0(X0,X1,X3)
% 7.45/1.50      | ~ l1_waybel_0(X1,X0)
% 7.45/1.50      | ~ r1_tarski(X2,X3)
% 7.45/1.50      | ~ l1_struct_0(X0)
% 7.45/1.50      | v2_struct_0(X0)
% 7.45/1.50      | v2_struct_0(X1) ),
% 7.45/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1367,plain,
% 7.45/1.50      ( r1_waybel_0(X0,X1,X2) != iProver_top
% 7.45/1.50      | r1_waybel_0(X0,X1,X3) = iProver_top
% 7.45/1.50      | l1_waybel_0(X1,X0) != iProver_top
% 7.45/1.50      | r1_tarski(X2,X3) != iProver_top
% 7.45/1.50      | l1_struct_0(X0) != iProver_top
% 7.45/1.50      | v2_struct_0(X0) = iProver_top
% 7.45/1.50      | v2_struct_0(X1) = iProver_top ),
% 7.45/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_2552,plain,
% 7.45/1.50      ( r1_waybel_0(X0,X1,X2) = iProver_top
% 7.45/1.50      | r2_waybel_0(X0,X1,X3) = iProver_top
% 7.45/1.50      | l1_waybel_0(X1,X0) != iProver_top
% 7.45/1.50      | r1_tarski(k6_subset_1(u1_struct_0(X0),X3),X2) != iProver_top
% 7.45/1.50      | l1_struct_0(X0) != iProver_top
% 7.45/1.50      | v2_struct_0(X0) = iProver_top
% 7.45/1.50      | v2_struct_0(X1) = iProver_top ),
% 7.45/1.50      inference(superposition,[status(thm)],[c_1370,c_1367]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_4194,plain,
% 7.45/1.50      ( r1_waybel_0(X0,X1,u1_struct_0(X0)) = iProver_top
% 7.45/1.50      | r2_waybel_0(X0,X1,X2) = iProver_top
% 7.45/1.50      | l1_waybel_0(X1,X0) != iProver_top
% 7.45/1.50      | l1_struct_0(X0) != iProver_top
% 7.45/1.50      | v2_struct_0(X0) = iProver_top
% 7.45/1.50      | v2_struct_0(X1) = iProver_top ),
% 7.45/1.50      inference(superposition,[status(thm)],[c_4175,c_2552]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_25,negated_conjecture,
% 7.45/1.50      ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
% 7.45/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_1366,plain,
% 7.45/1.50      ( r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) != iProver_top ),
% 7.45/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_9259,plain,
% 7.45/1.50      ( r2_waybel_0(sK5,sK6,X0) = iProver_top
% 7.45/1.50      | l1_waybel_0(sK6,sK5) != iProver_top
% 7.45/1.50      | l1_struct_0(sK5) != iProver_top
% 7.45/1.50      | v2_struct_0(sK6) = iProver_top
% 7.45/1.50      | v2_struct_0(sK5) = iProver_top ),
% 7.45/1.50      inference(superposition,[status(thm)],[c_4194,c_1366]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_9273,plain,
% 7.45/1.50      ( r2_waybel_0(sK5,sK6,X0)
% 7.45/1.50      | ~ l1_waybel_0(sK6,sK5)
% 7.45/1.50      | ~ l1_struct_0(sK5)
% 7.45/1.50      | v2_struct_0(sK6)
% 7.45/1.50      | v2_struct_0(sK5) ),
% 7.45/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_9259]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_9388,plain,
% 7.45/1.50      ( ~ v1_xboole_0(X0) ),
% 7.45/1.50      inference(global_propositional_subsumption,
% 7.45/1.50                [status(thm)],
% 7.45/1.50                [c_5403,c_29,c_28,c_27,c_26,c_2189,c_2526,c_2623,c_3356,
% 7.45/1.50                 c_4032,c_4874,c_6871,c_9273]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_8,plain,
% 7.45/1.50      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
% 7.45/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_2846,plain,
% 7.45/1.50      ( ~ r2_hidden(sK0(k6_subset_1(X0,X1)),X1)
% 7.45/1.50      | v1_xboole_0(k6_subset_1(X0,X1)) ),
% 7.45/1.50      inference(resolution,[status(thm)],[c_8,c_0]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_2458,plain,
% 7.45/1.50      ( r2_hidden(sK0(k6_subset_1(X0,X1)),X0)
% 7.45/1.50      | v1_xboole_0(k6_subset_1(X0,X1)) ),
% 7.45/1.50      inference(resolution,[status(thm)],[c_9,c_0]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_2908,plain,
% 7.45/1.50      ( v1_xboole_0(k6_subset_1(X0,X0)) ),
% 7.45/1.50      inference(resolution,[status(thm)],[c_2846,c_2458]) ).
% 7.45/1.50  
% 7.45/1.50  cnf(c_23438,plain,
% 7.45/1.50      ( $false ),
% 7.45/1.50      inference(backward_subsumption_resolution,[status(thm)],[c_9388,c_2908]) ).
% 7.45/1.50  
% 7.45/1.50  
% 7.45/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.45/1.50  
% 7.45/1.50  ------                               Statistics
% 7.45/1.50  
% 7.45/1.50  ------ Selected
% 7.45/1.50  
% 7.45/1.50  total_time:                             0.803
% 7.45/1.50  
%------------------------------------------------------------------------------
