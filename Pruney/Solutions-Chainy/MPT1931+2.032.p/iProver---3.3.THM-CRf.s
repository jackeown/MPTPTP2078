%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:13 EST 2020

% Result     : Theorem 1.34s
% Output     : CNFRefutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 242 expanded)
%              Number of clauses        :   41 (  52 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  446 (1608 expanded)
%              Number of equality atoms :   44 ( 139 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK4,u1_struct_0(X0))
        & l1_waybel_0(sK4,X0)
        & v7_waybel_0(sK4)
        & v4_orders_2(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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

fof(f29,plain,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3))
    & l1_waybel_0(sK4,sK3)
    & v7_waybel_0(sK4)
    & v4_orders_2(sK4)
    & ~ v2_struct_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f28,f27])).

fof(f51,plain,(
    ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f24,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5))
        & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5))
                      & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f24,f23])).

fof(f39,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3550,plain,
    ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),X0)
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),k6_subset_1(X3,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3552,plain,
    ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),k6_subset_1(sK3,sK3))
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_3550])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_780,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_781,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1365,plain,
    ( k6_subset_1(X0,X0) = X1
    | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_781])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_777,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k6_subset_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1667,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
    | r2_hidden(sK0(X0,X0,k6_subset_1(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_777])).

cnf(c_778,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1668,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
    | r2_hidden(sK0(X0,X0,k6_subset_1(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_778])).

cnf(c_2171,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X1) ),
    inference(superposition,[status(thm)],[c_1667,c_1668])).

cnf(c_11,plain,
    ( r1_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_309,plain,
    ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | u1_struct_0(sK3) != X2
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_310,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ l1_waybel_0(sK4,sK3)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_312,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_20,c_19,c_18,c_15])).

cnf(c_767,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_2345,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2171,c_767])).

cnf(c_2366,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(X0,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2345])).

cnf(c_2368,plain,
    ( r2_waybel_0(sK3,sK4,k6_subset_1(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_1648,plain,
    ( r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),X0)
    | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1654,plain,
    ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),k6_subset_1(sK3,sK3))
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),sK3) ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_8,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_952,plain,
    ( ~ r2_waybel_0(sK3,sK4,X0)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,X1)),X0)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1015,plain,
    ( ~ r2_waybel_0(sK3,sK4,X0)
    | ~ l1_waybel_0(sK4,sK3)
    | ~ m1_subset_1(o_2_2_yellow_6(X1,sK4),u1_struct_0(sK4))
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,o_2_2_yellow_6(X1,sK4))),X0)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_952])).

cnf(c_1647,plain,
    ( ~ r2_waybel_0(sK3,sK4,k6_subset_1(X0,X1))
    | ~ l1_waybel_0(sK4,sK3)
    | ~ m1_subset_1(o_2_2_yellow_6(X2,sK4),u1_struct_0(sK4))
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),k6_subset_1(X0,X1))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1015])).

cnf(c_1650,plain,
    ( ~ r2_waybel_0(sK3,sK4,k6_subset_1(sK3,sK3))
    | ~ l1_waybel_0(sK4,sK3)
    | ~ m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4))
    | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),k6_subset_1(sK3,sK3))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_13,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(o_2_2_yellow_6(X1,X0),u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_229,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(o_2_2_yellow_6(X1,X0),u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_230,plain,
    ( ~ l1_waybel_0(sK4,X0)
    | m1_subset_1(o_2_2_yellow_6(X0,sK4),u1_struct_0(sK4))
    | ~ v4_orders_2(sK4)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_232,plain,
    ( ~ l1_waybel_0(sK4,sK3)
    | m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4))
    | ~ v4_orders_2(sK4)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_17,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3552,c_2368,c_1654,c_1650,c_232,c_15,c_17,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.09  % Command    : iproveropt_run.sh %d %s
% 0.07/0.28  % Computer   : n010.cluster.edu
% 0.07/0.28  % Model      : x86_64 x86_64
% 0.07/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.28  % Memory     : 8042.1875MB
% 0.07/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.28  % CPULimit   : 60
% 0.07/0.28  % WCLimit    : 600
% 0.07/0.28  % DateTime   : Tue Dec  1 11:06:44 EST 2020
% 0.07/0.28  % CPUTime    : 
% 0.07/0.28  % Running in FOF mode
% 1.34/0.90  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.34/0.90  
% 1.34/0.90  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.34/0.90  
% 1.34/0.90  ------  iProver source info
% 1.34/0.90  
% 1.34/0.90  git: date: 2020-06-30 10:37:57 +0100
% 1.34/0.90  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.34/0.90  git: non_committed_changes: false
% 1.34/0.90  git: last_make_outside_of_git: false
% 1.34/0.90  
% 1.34/0.90  ------ 
% 1.34/0.90  
% 1.34/0.90  ------ Input Options
% 1.34/0.90  
% 1.34/0.90  --out_options                           all
% 1.34/0.90  --tptp_safe_out                         true
% 1.34/0.90  --problem_path                          ""
% 1.34/0.90  --include_path                          ""
% 1.34/0.90  --clausifier                            res/vclausify_rel
% 1.34/0.90  --clausifier_options                    --mode clausify
% 1.34/0.90  --stdin                                 false
% 1.34/0.90  --stats_out                             all
% 1.34/0.90  
% 1.34/0.90  ------ General Options
% 1.34/0.90  
% 1.34/0.90  --fof                                   false
% 1.34/0.90  --time_out_real                         305.
% 1.34/0.90  --time_out_virtual                      -1.
% 1.34/0.90  --symbol_type_check                     false
% 1.34/0.90  --clausify_out                          false
% 1.34/0.90  --sig_cnt_out                           false
% 1.34/0.90  --trig_cnt_out                          false
% 1.34/0.90  --trig_cnt_out_tolerance                1.
% 1.34/0.90  --trig_cnt_out_sk_spl                   false
% 1.34/0.90  --abstr_cl_out                          false
% 1.34/0.90  
% 1.34/0.90  ------ Global Options
% 1.34/0.90  
% 1.34/0.90  --schedule                              default
% 1.34/0.90  --add_important_lit                     false
% 1.34/0.90  --prop_solver_per_cl                    1000
% 1.34/0.90  --min_unsat_core                        false
% 1.34/0.90  --soft_assumptions                      false
% 1.34/0.90  --soft_lemma_size                       3
% 1.34/0.90  --prop_impl_unit_size                   0
% 1.34/0.90  --prop_impl_unit                        []
% 1.34/0.90  --share_sel_clauses                     true
% 1.34/0.90  --reset_solvers                         false
% 1.34/0.90  --bc_imp_inh                            [conj_cone]
% 1.34/0.90  --conj_cone_tolerance                   3.
% 1.34/0.90  --extra_neg_conj                        none
% 1.34/0.90  --large_theory_mode                     true
% 1.34/0.90  --prolific_symb_bound                   200
% 1.34/0.90  --lt_threshold                          2000
% 1.34/0.90  --clause_weak_htbl                      true
% 1.34/0.90  --gc_record_bc_elim                     false
% 1.34/0.90  
% 1.34/0.90  ------ Preprocessing Options
% 1.34/0.90  
% 1.34/0.90  --preprocessing_flag                    true
% 1.34/0.90  --time_out_prep_mult                    0.1
% 1.34/0.90  --splitting_mode                        input
% 1.34/0.90  --splitting_grd                         true
% 1.34/0.90  --splitting_cvd                         false
% 1.34/0.90  --splitting_cvd_svl                     false
% 1.34/0.90  --splitting_nvd                         32
% 1.34/0.90  --sub_typing                            true
% 1.34/0.90  --prep_gs_sim                           true
% 1.34/0.90  --prep_unflatten                        true
% 1.34/0.90  --prep_res_sim                          true
% 1.34/0.90  --prep_upred                            true
% 1.34/0.90  --prep_sem_filter                       exhaustive
% 1.34/0.90  --prep_sem_filter_out                   false
% 1.34/0.90  --pred_elim                             true
% 1.34/0.90  --res_sim_input                         true
% 1.34/0.90  --eq_ax_congr_red                       true
% 1.34/0.90  --pure_diseq_elim                       true
% 1.34/0.90  --brand_transform                       false
% 1.34/0.90  --non_eq_to_eq                          false
% 1.34/0.90  --prep_def_merge                        true
% 1.34/0.90  --prep_def_merge_prop_impl              false
% 1.34/0.90  --prep_def_merge_mbd                    true
% 1.34/0.90  --prep_def_merge_tr_red                 false
% 1.34/0.90  --prep_def_merge_tr_cl                  false
% 1.34/0.90  --smt_preprocessing                     true
% 1.34/0.90  --smt_ac_axioms                         fast
% 1.34/0.90  --preprocessed_out                      false
% 1.34/0.90  --preprocessed_stats                    false
% 1.34/0.90  
% 1.34/0.90  ------ Abstraction refinement Options
% 1.34/0.90  
% 1.34/0.90  --abstr_ref                             []
% 1.34/0.90  --abstr_ref_prep                        false
% 1.34/0.90  --abstr_ref_until_sat                   false
% 1.34/0.90  --abstr_ref_sig_restrict                funpre
% 1.34/0.90  --abstr_ref_af_restrict_to_split_sk     false
% 1.34/0.90  --abstr_ref_under                       []
% 1.34/0.90  
% 1.34/0.90  ------ SAT Options
% 1.34/0.90  
% 1.34/0.90  --sat_mode                              false
% 1.34/0.90  --sat_fm_restart_options                ""
% 1.34/0.90  --sat_gr_def                            false
% 1.34/0.90  --sat_epr_types                         true
% 1.34/0.90  --sat_non_cyclic_types                  false
% 1.34/0.90  --sat_finite_models                     false
% 1.34/0.90  --sat_fm_lemmas                         false
% 1.34/0.90  --sat_fm_prep                           false
% 1.34/0.90  --sat_fm_uc_incr                        true
% 1.34/0.90  --sat_out_model                         small
% 1.34/0.90  --sat_out_clauses                       false
% 1.34/0.90  
% 1.34/0.90  ------ QBF Options
% 1.34/0.90  
% 1.34/0.90  --qbf_mode                              false
% 1.34/0.90  --qbf_elim_univ                         false
% 1.34/0.90  --qbf_dom_inst                          none
% 1.34/0.90  --qbf_dom_pre_inst                      false
% 1.34/0.90  --qbf_sk_in                             false
% 1.34/0.90  --qbf_pred_elim                         true
% 1.34/0.90  --qbf_split                             512
% 1.34/0.90  
% 1.34/0.90  ------ BMC1 Options
% 1.34/0.90  
% 1.34/0.90  --bmc1_incremental                      false
% 1.34/0.90  --bmc1_axioms                           reachable_all
% 1.34/0.90  --bmc1_min_bound                        0
% 1.34/0.90  --bmc1_max_bound                        -1
% 1.34/0.90  --bmc1_max_bound_default                -1
% 1.34/0.90  --bmc1_symbol_reachability              true
% 1.34/0.90  --bmc1_property_lemmas                  false
% 1.34/0.90  --bmc1_k_induction                      false
% 1.34/0.90  --bmc1_non_equiv_states                 false
% 1.34/0.90  --bmc1_deadlock                         false
% 1.34/0.90  --bmc1_ucm                              false
% 1.34/0.90  --bmc1_add_unsat_core                   none
% 1.34/0.90  --bmc1_unsat_core_children              false
% 1.34/0.90  --bmc1_unsat_core_extrapolate_axioms    false
% 1.34/0.90  --bmc1_out_stat                         full
% 1.34/0.90  --bmc1_ground_init                      false
% 1.34/0.90  --bmc1_pre_inst_next_state              false
% 1.34/0.90  --bmc1_pre_inst_state                   false
% 1.34/0.90  --bmc1_pre_inst_reach_state             false
% 1.34/0.90  --bmc1_out_unsat_core                   false
% 1.34/0.90  --bmc1_aig_witness_out                  false
% 1.34/0.90  --bmc1_verbose                          false
% 1.34/0.90  --bmc1_dump_clauses_tptp                false
% 1.34/0.90  --bmc1_dump_unsat_core_tptp             false
% 1.34/0.90  --bmc1_dump_file                        -
% 1.34/0.90  --bmc1_ucm_expand_uc_limit              128
% 1.34/0.90  --bmc1_ucm_n_expand_iterations          6
% 1.34/0.90  --bmc1_ucm_extend_mode                  1
% 1.34/0.90  --bmc1_ucm_init_mode                    2
% 1.34/0.90  --bmc1_ucm_cone_mode                    none
% 1.34/0.90  --bmc1_ucm_reduced_relation_type        0
% 1.34/0.90  --bmc1_ucm_relax_model                  4
% 1.34/0.90  --bmc1_ucm_full_tr_after_sat            true
% 1.34/0.90  --bmc1_ucm_expand_neg_assumptions       false
% 1.34/0.90  --bmc1_ucm_layered_model                none
% 1.34/0.90  --bmc1_ucm_max_lemma_size               10
% 1.34/0.90  
% 1.34/0.90  ------ AIG Options
% 1.34/0.90  
% 1.34/0.90  --aig_mode                              false
% 1.34/0.90  
% 1.34/0.90  ------ Instantiation Options
% 1.34/0.90  
% 1.34/0.90  --instantiation_flag                    true
% 1.34/0.90  --inst_sos_flag                         false
% 1.34/0.90  --inst_sos_phase                        true
% 1.34/0.90  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.34/0.90  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.34/0.90  --inst_lit_sel_side                     num_symb
% 1.34/0.90  --inst_solver_per_active                1400
% 1.34/0.90  --inst_solver_calls_frac                1.
% 1.34/0.90  --inst_passive_queue_type               priority_queues
% 1.34/0.90  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.34/0.90  --inst_passive_queues_freq              [25;2]
% 1.34/0.90  --inst_dismatching                      true
% 1.34/0.90  --inst_eager_unprocessed_to_passive     true
% 1.34/0.90  --inst_prop_sim_given                   true
% 1.34/0.90  --inst_prop_sim_new                     false
% 1.34/0.90  --inst_subs_new                         false
% 1.34/0.90  --inst_eq_res_simp                      false
% 1.34/0.90  --inst_subs_given                       false
% 1.34/0.90  --inst_orphan_elimination               true
% 1.34/0.90  --inst_learning_loop_flag               true
% 1.34/0.90  --inst_learning_start                   3000
% 1.34/0.90  --inst_learning_factor                  2
% 1.34/0.90  --inst_start_prop_sim_after_learn       3
% 1.34/0.90  --inst_sel_renew                        solver
% 1.34/0.90  --inst_lit_activity_flag                true
% 1.34/0.90  --inst_restr_to_given                   false
% 1.34/0.90  --inst_activity_threshold               500
% 1.34/0.90  --inst_out_proof                        true
% 1.34/0.90  
% 1.34/0.90  ------ Resolution Options
% 1.34/0.90  
% 1.34/0.90  --resolution_flag                       true
% 1.34/0.90  --res_lit_sel                           adaptive
% 1.34/0.90  --res_lit_sel_side                      none
% 1.34/0.90  --res_ordering                          kbo
% 1.34/0.90  --res_to_prop_solver                    active
% 1.34/0.90  --res_prop_simpl_new                    false
% 1.34/0.90  --res_prop_simpl_given                  true
% 1.34/0.90  --res_passive_queue_type                priority_queues
% 1.34/0.90  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.34/0.90  --res_passive_queues_freq               [15;5]
% 1.34/0.90  --res_forward_subs                      full
% 1.34/0.90  --res_backward_subs                     full
% 1.34/0.90  --res_forward_subs_resolution           true
% 1.34/0.90  --res_backward_subs_resolution          true
% 1.34/0.90  --res_orphan_elimination                true
% 1.34/0.90  --res_time_limit                        2.
% 1.34/0.90  --res_out_proof                         true
% 1.34/0.90  
% 1.34/0.90  ------ Superposition Options
% 1.34/0.90  
% 1.34/0.90  --superposition_flag                    true
% 1.34/0.90  --sup_passive_queue_type                priority_queues
% 1.34/0.90  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.34/0.90  --sup_passive_queues_freq               [8;1;4]
% 1.34/0.90  --demod_completeness_check              fast
% 1.34/0.90  --demod_use_ground                      true
% 1.34/0.90  --sup_to_prop_solver                    passive
% 1.34/0.90  --sup_prop_simpl_new                    true
% 1.34/0.90  --sup_prop_simpl_given                  true
% 1.34/0.90  --sup_fun_splitting                     false
% 1.34/0.90  --sup_smt_interval                      50000
% 1.34/0.90  
% 1.34/0.90  ------ Superposition Simplification Setup
% 1.34/0.90  
% 1.34/0.90  --sup_indices_passive                   []
% 1.34/0.90  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.90  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.90  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.90  --sup_full_triv                         [TrivRules;PropSubs]
% 1.34/0.90  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.90  --sup_full_bw                           [BwDemod]
% 1.34/0.90  --sup_immed_triv                        [TrivRules]
% 1.34/0.90  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.34/0.90  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.90  --sup_immed_bw_main                     []
% 1.34/0.90  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.90  --sup_input_triv                        [Unflattening;TrivRules]
% 1.34/0.90  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.90  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.90  
% 1.34/0.90  ------ Combination Options
% 1.34/0.90  
% 1.34/0.90  --comb_res_mult                         3
% 1.34/0.90  --comb_sup_mult                         2
% 1.34/0.90  --comb_inst_mult                        10
% 1.34/0.90  
% 1.34/0.90  ------ Debug Options
% 1.34/0.90  
% 1.34/0.90  --dbg_backtrace                         false
% 1.34/0.90  --dbg_dump_prop_clauses                 false
% 1.34/0.90  --dbg_dump_prop_clauses_file            -
% 1.34/0.90  --dbg_out_stat                          false
% 1.34/0.90  ------ Parsing...
% 1.34/0.90  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.34/0.90  
% 1.34/0.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.34/0.90  
% 1.34/0.90  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.34/0.90  
% 1.34/0.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.34/0.90  ------ Proving...
% 1.34/0.90  ------ Problem Properties 
% 1.34/0.90  
% 1.34/0.90  
% 1.34/0.90  clauses                                 16
% 1.34/0.90  conjectures                             4
% 1.34/0.90  EPR                                     4
% 1.34/0.90  Horn                                    7
% 1.34/0.90  unary                                   5
% 1.34/0.90  binary                                  2
% 1.34/0.90  lits                                    56
% 1.34/0.90  lits eq                                 3
% 1.34/0.90  fd_pure                                 0
% 1.34/0.90  fd_pseudo                               0
% 1.34/0.90  fd_cond                                 0
% 1.34/0.90  fd_pseudo_cond                          3
% 1.34/0.90  AC symbols                              0
% 1.34/0.90  
% 1.34/0.90  ------ Schedule dynamic 5 is on 
% 1.34/0.90  
% 1.34/0.90  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.34/0.90  
% 1.34/0.90  
% 1.34/0.90  ------ 
% 1.34/0.90  Current options:
% 1.34/0.90  ------ 
% 1.34/0.90  
% 1.34/0.90  ------ Input Options
% 1.34/0.90  
% 1.34/0.90  --out_options                           all
% 1.34/0.90  --tptp_safe_out                         true
% 1.34/0.90  --problem_path                          ""
% 1.34/0.90  --include_path                          ""
% 1.34/0.90  --clausifier                            res/vclausify_rel
% 1.34/0.90  --clausifier_options                    --mode clausify
% 1.34/0.90  --stdin                                 false
% 1.34/0.90  --stats_out                             all
% 1.34/0.90  
% 1.34/0.90  ------ General Options
% 1.34/0.90  
% 1.34/0.90  --fof                                   false
% 1.34/0.90  --time_out_real                         305.
% 1.34/0.90  --time_out_virtual                      -1.
% 1.34/0.90  --symbol_type_check                     false
% 1.34/0.90  --clausify_out                          false
% 1.34/0.90  --sig_cnt_out                           false
% 1.34/0.90  --trig_cnt_out                          false
% 1.34/0.90  --trig_cnt_out_tolerance                1.
% 1.34/0.90  --trig_cnt_out_sk_spl                   false
% 1.34/0.90  --abstr_cl_out                          false
% 1.34/0.90  
% 1.34/0.90  ------ Global Options
% 1.34/0.90  
% 1.34/0.90  --schedule                              default
% 1.34/0.90  --add_important_lit                     false
% 1.34/0.90  --prop_solver_per_cl                    1000
% 1.34/0.90  --min_unsat_core                        false
% 1.34/0.90  --soft_assumptions                      false
% 1.34/0.90  --soft_lemma_size                       3
% 1.34/0.90  --prop_impl_unit_size                   0
% 1.34/0.90  --prop_impl_unit                        []
% 1.34/0.90  --share_sel_clauses                     true
% 1.34/0.90  --reset_solvers                         false
% 1.34/0.90  --bc_imp_inh                            [conj_cone]
% 1.34/0.90  --conj_cone_tolerance                   3.
% 1.34/0.90  --extra_neg_conj                        none
% 1.34/0.90  --large_theory_mode                     true
% 1.34/0.90  --prolific_symb_bound                   200
% 1.34/0.90  --lt_threshold                          2000
% 1.34/0.90  --clause_weak_htbl                      true
% 1.34/0.90  --gc_record_bc_elim                     false
% 1.34/0.90  
% 1.34/0.90  ------ Preprocessing Options
% 1.34/0.90  
% 1.34/0.90  --preprocessing_flag                    true
% 1.34/0.90  --time_out_prep_mult                    0.1
% 1.34/0.90  --splitting_mode                        input
% 1.34/0.90  --splitting_grd                         true
% 1.34/0.90  --splitting_cvd                         false
% 1.34/0.90  --splitting_cvd_svl                     false
% 1.34/0.90  --splitting_nvd                         32
% 1.34/0.90  --sub_typing                            true
% 1.34/0.90  --prep_gs_sim                           true
% 1.34/0.90  --prep_unflatten                        true
% 1.34/0.90  --prep_res_sim                          true
% 1.34/0.90  --prep_upred                            true
% 1.34/0.90  --prep_sem_filter                       exhaustive
% 1.34/0.90  --prep_sem_filter_out                   false
% 1.34/0.90  --pred_elim                             true
% 1.34/0.90  --res_sim_input                         true
% 1.34/0.90  --eq_ax_congr_red                       true
% 1.34/0.90  --pure_diseq_elim                       true
% 1.34/0.90  --brand_transform                       false
% 1.34/0.90  --non_eq_to_eq                          false
% 1.34/0.90  --prep_def_merge                        true
% 1.34/0.90  --prep_def_merge_prop_impl              false
% 1.34/0.90  --prep_def_merge_mbd                    true
% 1.34/0.90  --prep_def_merge_tr_red                 false
% 1.34/0.90  --prep_def_merge_tr_cl                  false
% 1.34/0.90  --smt_preprocessing                     true
% 1.34/0.90  --smt_ac_axioms                         fast
% 1.34/0.90  --preprocessed_out                      false
% 1.34/0.90  --preprocessed_stats                    false
% 1.34/0.90  
% 1.34/0.90  ------ Abstraction refinement Options
% 1.34/0.90  
% 1.34/0.90  --abstr_ref                             []
% 1.34/0.90  --abstr_ref_prep                        false
% 1.34/0.90  --abstr_ref_until_sat                   false
% 1.34/0.90  --abstr_ref_sig_restrict                funpre
% 1.34/0.90  --abstr_ref_af_restrict_to_split_sk     false
% 1.34/0.90  --abstr_ref_under                       []
% 1.34/0.90  
% 1.34/0.90  ------ SAT Options
% 1.34/0.90  
% 1.34/0.90  --sat_mode                              false
% 1.34/0.90  --sat_fm_restart_options                ""
% 1.34/0.90  --sat_gr_def                            false
% 1.34/0.90  --sat_epr_types                         true
% 1.34/0.90  --sat_non_cyclic_types                  false
% 1.34/0.90  --sat_finite_models                     false
% 1.34/0.90  --sat_fm_lemmas                         false
% 1.34/0.90  --sat_fm_prep                           false
% 1.34/0.90  --sat_fm_uc_incr                        true
% 1.34/0.90  --sat_out_model                         small
% 1.34/0.90  --sat_out_clauses                       false
% 1.34/0.90  
% 1.34/0.90  ------ QBF Options
% 1.34/0.90  
% 1.34/0.90  --qbf_mode                              false
% 1.34/0.90  --qbf_elim_univ                         false
% 1.34/0.90  --qbf_dom_inst                          none
% 1.34/0.90  --qbf_dom_pre_inst                      false
% 1.34/0.90  --qbf_sk_in                             false
% 1.34/0.90  --qbf_pred_elim                         true
% 1.34/0.90  --qbf_split                             512
% 1.34/0.90  
% 1.34/0.90  ------ BMC1 Options
% 1.34/0.90  
% 1.34/0.90  --bmc1_incremental                      false
% 1.34/0.90  --bmc1_axioms                           reachable_all
% 1.34/0.90  --bmc1_min_bound                        0
% 1.34/0.90  --bmc1_max_bound                        -1
% 1.34/0.90  --bmc1_max_bound_default                -1
% 1.34/0.90  --bmc1_symbol_reachability              true
% 1.34/0.90  --bmc1_property_lemmas                  false
% 1.34/0.90  --bmc1_k_induction                      false
% 1.34/0.90  --bmc1_non_equiv_states                 false
% 1.34/0.90  --bmc1_deadlock                         false
% 1.34/0.90  --bmc1_ucm                              false
% 1.34/0.90  --bmc1_add_unsat_core                   none
% 1.34/0.90  --bmc1_unsat_core_children              false
% 1.34/0.90  --bmc1_unsat_core_extrapolate_axioms    false
% 1.34/0.90  --bmc1_out_stat                         full
% 1.34/0.90  --bmc1_ground_init                      false
% 1.34/0.90  --bmc1_pre_inst_next_state              false
% 1.34/0.90  --bmc1_pre_inst_state                   false
% 1.34/0.90  --bmc1_pre_inst_reach_state             false
% 1.34/0.90  --bmc1_out_unsat_core                   false
% 1.34/0.90  --bmc1_aig_witness_out                  false
% 1.34/0.90  --bmc1_verbose                          false
% 1.34/0.90  --bmc1_dump_clauses_tptp                false
% 1.34/0.90  --bmc1_dump_unsat_core_tptp             false
% 1.34/0.90  --bmc1_dump_file                        -
% 1.34/0.90  --bmc1_ucm_expand_uc_limit              128
% 1.34/0.90  --bmc1_ucm_n_expand_iterations          6
% 1.34/0.90  --bmc1_ucm_extend_mode                  1
% 1.34/0.90  --bmc1_ucm_init_mode                    2
% 1.34/0.90  --bmc1_ucm_cone_mode                    none
% 1.34/0.90  --bmc1_ucm_reduced_relation_type        0
% 1.34/0.90  --bmc1_ucm_relax_model                  4
% 1.34/0.90  --bmc1_ucm_full_tr_after_sat            true
% 1.34/0.90  --bmc1_ucm_expand_neg_assumptions       false
% 1.34/0.90  --bmc1_ucm_layered_model                none
% 1.34/0.90  --bmc1_ucm_max_lemma_size               10
% 1.34/0.90  
% 1.34/0.90  ------ AIG Options
% 1.34/0.90  
% 1.34/0.90  --aig_mode                              false
% 1.34/0.90  
% 1.34/0.90  ------ Instantiation Options
% 1.34/0.90  
% 1.34/0.90  --instantiation_flag                    true
% 1.34/0.90  --inst_sos_flag                         false
% 1.34/0.90  --inst_sos_phase                        true
% 1.34/0.90  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.34/0.90  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.34/0.90  --inst_lit_sel_side                     none
% 1.34/0.90  --inst_solver_per_active                1400
% 1.34/0.90  --inst_solver_calls_frac                1.
% 1.34/0.90  --inst_passive_queue_type               priority_queues
% 1.34/0.90  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.34/0.90  --inst_passive_queues_freq              [25;2]
% 1.34/0.90  --inst_dismatching                      true
% 1.34/0.90  --inst_eager_unprocessed_to_passive     true
% 1.34/0.90  --inst_prop_sim_given                   true
% 1.34/0.90  --inst_prop_sim_new                     false
% 1.34/0.90  --inst_subs_new                         false
% 1.34/0.90  --inst_eq_res_simp                      false
% 1.34/0.90  --inst_subs_given                       false
% 1.34/0.90  --inst_orphan_elimination               true
% 1.34/0.90  --inst_learning_loop_flag               true
% 1.34/0.90  --inst_learning_start                   3000
% 1.34/0.90  --inst_learning_factor                  2
% 1.34/0.90  --inst_start_prop_sim_after_learn       3
% 1.34/0.90  --inst_sel_renew                        solver
% 1.34/0.90  --inst_lit_activity_flag                true
% 1.34/0.90  --inst_restr_to_given                   false
% 1.34/0.90  --inst_activity_threshold               500
% 1.34/0.90  --inst_out_proof                        true
% 1.34/0.90  
% 1.34/0.90  ------ Resolution Options
% 1.34/0.90  
% 1.34/0.90  --resolution_flag                       false
% 1.34/0.90  --res_lit_sel                           adaptive
% 1.34/0.90  --res_lit_sel_side                      none
% 1.34/0.90  --res_ordering                          kbo
% 1.34/0.90  --res_to_prop_solver                    active
% 1.34/0.90  --res_prop_simpl_new                    false
% 1.34/0.90  --res_prop_simpl_given                  true
% 1.34/0.90  --res_passive_queue_type                priority_queues
% 1.34/0.90  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.34/0.90  --res_passive_queues_freq               [15;5]
% 1.34/0.90  --res_forward_subs                      full
% 1.34/0.90  --res_backward_subs                     full
% 1.34/0.90  --res_forward_subs_resolution           true
% 1.34/0.90  --res_backward_subs_resolution          true
% 1.34/0.90  --res_orphan_elimination                true
% 1.34/0.90  --res_time_limit                        2.
% 1.34/0.90  --res_out_proof                         true
% 1.34/0.90  
% 1.34/0.90  ------ Superposition Options
% 1.34/0.90  
% 1.34/0.90  --superposition_flag                    true
% 1.34/0.90  --sup_passive_queue_type                priority_queues
% 1.34/0.90  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.34/0.90  --sup_passive_queues_freq               [8;1;4]
% 1.34/0.90  --demod_completeness_check              fast
% 1.34/0.90  --demod_use_ground                      true
% 1.34/0.90  --sup_to_prop_solver                    passive
% 1.34/0.90  --sup_prop_simpl_new                    true
% 1.34/0.90  --sup_prop_simpl_given                  true
% 1.34/0.90  --sup_fun_splitting                     false
% 1.34/0.90  --sup_smt_interval                      50000
% 1.34/0.90  
% 1.34/0.90  ------ Superposition Simplification Setup
% 1.34/0.90  
% 1.34/0.90  --sup_indices_passive                   []
% 1.34/0.90  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.90  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.90  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.90  --sup_full_triv                         [TrivRules;PropSubs]
% 1.34/0.90  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.90  --sup_full_bw                           [BwDemod]
% 1.34/0.90  --sup_immed_triv                        [TrivRules]
% 1.34/0.90  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.34/0.90  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.90  --sup_immed_bw_main                     []
% 1.34/0.90  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.90  --sup_input_triv                        [Unflattening;TrivRules]
% 1.34/0.90  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.90  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.90  
% 1.34/0.90  ------ Combination Options
% 1.34/0.90  
% 1.34/0.90  --comb_res_mult                         3
% 1.34/0.90  --comb_sup_mult                         2
% 1.34/0.90  --comb_inst_mult                        10
% 1.34/0.90  
% 1.34/0.90  ------ Debug Options
% 1.34/0.90  
% 1.34/0.90  --dbg_backtrace                         false
% 1.34/0.90  --dbg_dump_prop_clauses                 false
% 1.34/0.90  --dbg_dump_prop_clauses_file            -
% 1.34/0.90  --dbg_out_stat                          false
% 1.34/0.90  
% 1.34/0.90  
% 1.34/0.90  
% 1.34/0.90  
% 1.34/0.90  ------ Proving...
% 1.34/0.90  
% 1.34/0.90  
% 1.34/0.90  % SZS status Theorem for theBenchmark.p
% 1.34/0.90  
% 1.34/0.90  % SZS output start CNFRefutation for theBenchmark.p
% 1.34/0.90  
% 1.34/0.90  fof(f1,axiom,(
% 1.34/0.90    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.34/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.90  
% 1.34/0.90  fof(f16,plain,(
% 1.34/0.90    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.90    inference(nnf_transformation,[],[f1])).
% 1.34/0.90  
% 1.34/0.90  fof(f17,plain,(
% 1.34/0.90    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.90    inference(flattening,[],[f16])).
% 1.34/0.90  
% 1.34/0.90  fof(f18,plain,(
% 1.34/0.90    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.90    inference(rectify,[],[f17])).
% 1.34/0.90  
% 1.34/0.90  fof(f19,plain,(
% 1.34/0.90    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.34/0.90    introduced(choice_axiom,[])).
% 1.34/0.90  
% 1.34/0.90  fof(f20,plain,(
% 1.34/0.90    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.34/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 1.34/0.90  
% 1.34/0.90  fof(f31,plain,(
% 1.34/0.90    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.90    inference(cnf_transformation,[],[f20])).
% 1.34/0.90  
% 1.34/0.90  fof(f2,axiom,(
% 1.34/0.90    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.34/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.90  
% 1.34/0.90  fof(f36,plain,(
% 1.34/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.34/0.90    inference(cnf_transformation,[],[f2])).
% 1.34/0.90  
% 1.34/0.90  fof(f56,plain,(
% 1.34/0.90    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.34/0.90    inference(definition_unfolding,[],[f31,f36])).
% 1.34/0.90  
% 1.34/0.90  fof(f59,plain,(
% 1.34/0.90    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 1.34/0.90    inference(equality_resolution,[],[f56])).
% 1.34/0.90  
% 1.34/0.90  fof(f33,plain,(
% 1.34/0.90    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 1.34/0.90    inference(cnf_transformation,[],[f20])).
% 1.34/0.90  
% 1.34/0.90  fof(f54,plain,(
% 1.34/0.90    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 1.34/0.90    inference(definition_unfolding,[],[f33,f36])).
% 1.34/0.90  
% 1.34/0.90  fof(f34,plain,(
% 1.34/0.90    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 1.34/0.90    inference(cnf_transformation,[],[f20])).
% 1.34/0.90  
% 1.34/0.90  fof(f53,plain,(
% 1.34/0.90    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 1.34/0.90    inference(definition_unfolding,[],[f34,f36])).
% 1.34/0.90  
% 1.34/0.90  fof(f30,plain,(
% 1.34/0.90    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.34/0.90    inference(cnf_transformation,[],[f20])).
% 1.34/0.90  
% 1.34/0.90  fof(f57,plain,(
% 1.34/0.90    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.34/0.90    inference(definition_unfolding,[],[f30,f36])).
% 1.34/0.90  
% 1.34/0.90  fof(f60,plain,(
% 1.34/0.90    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 1.34/0.90    inference(equality_resolution,[],[f57])).
% 1.34/0.90  
% 1.34/0.90  fof(f4,axiom,(
% 1.34/0.90    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.34/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.90  
% 1.34/0.90  fof(f10,plain,(
% 1.34/0.90    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.34/0.90    inference(ennf_transformation,[],[f4])).
% 1.34/0.90  
% 1.34/0.90  fof(f11,plain,(
% 1.34/0.90    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.34/0.90    inference(flattening,[],[f10])).
% 1.34/0.90  
% 1.34/0.90  fof(f26,plain,(
% 1.34/0.90    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.34/0.90    inference(nnf_transformation,[],[f11])).
% 1.34/0.90  
% 1.34/0.90  fof(f43,plain,(
% 1.34/0.90    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.34/0.90    inference(cnf_transformation,[],[f26])).
% 1.34/0.90  
% 1.34/0.90  fof(f6,conjecture,(
% 1.34/0.90    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.34/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.90  
% 1.34/0.90  fof(f7,negated_conjecture,(
% 1.34/0.90    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.34/0.90    inference(negated_conjecture,[],[f6])).
% 1.34/0.90  
% 1.34/0.90  fof(f14,plain,(
% 1.34/0.90    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.34/0.90    inference(ennf_transformation,[],[f7])).
% 1.34/0.90  
% 1.34/0.90  fof(f15,plain,(
% 1.34/0.90    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.34/0.90    inference(flattening,[],[f14])).
% 1.34/0.90  
% 1.34/0.90  fof(f28,plain,(
% 1.34/0.90    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK4,u1_struct_0(X0)) & l1_waybel_0(sK4,X0) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4))) )),
% 1.34/0.90    introduced(choice_axiom,[])).
% 1.34/0.90  
% 1.34/0.90  fof(f27,plain,(
% 1.34/0.90    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK3,X1,u1_struct_0(sK3)) & l1_waybel_0(X1,sK3) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 1.34/0.90    introduced(choice_axiom,[])).
% 1.34/0.90  
% 1.34/0.90  fof(f29,plain,(
% 1.34/0.90    (~r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) & l1_waybel_0(sK4,sK3) & v7_waybel_0(sK4) & v4_orders_2(sK4) & ~v2_struct_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 1.34/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f28,f27])).
% 1.34/0.90  
% 1.34/0.90  fof(f51,plain,(
% 1.34/0.90    ~r1_waybel_0(sK3,sK4,u1_struct_0(sK3))),
% 1.34/0.90    inference(cnf_transformation,[],[f29])).
% 1.34/0.90  
% 1.34/0.90  fof(f45,plain,(
% 1.34/0.90    ~v2_struct_0(sK3)),
% 1.34/0.90    inference(cnf_transformation,[],[f29])).
% 1.34/0.90  
% 1.34/0.90  fof(f46,plain,(
% 1.34/0.90    l1_struct_0(sK3)),
% 1.34/0.90    inference(cnf_transformation,[],[f29])).
% 1.34/0.90  
% 1.34/0.90  fof(f47,plain,(
% 1.34/0.90    ~v2_struct_0(sK4)),
% 1.34/0.90    inference(cnf_transformation,[],[f29])).
% 1.34/0.90  
% 1.34/0.90  fof(f50,plain,(
% 1.34/0.90    l1_waybel_0(sK4,sK3)),
% 1.34/0.90    inference(cnf_transformation,[],[f29])).
% 1.34/0.90  
% 1.34/0.90  fof(f3,axiom,(
% 1.34/0.90    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.34/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.90  
% 1.34/0.90  fof(f8,plain,(
% 1.34/0.90    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.34/0.90    inference(ennf_transformation,[],[f3])).
% 1.34/0.90  
% 1.34/0.90  fof(f9,plain,(
% 1.34/0.90    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.34/0.90    inference(flattening,[],[f8])).
% 1.34/0.90  
% 1.34/0.90  fof(f21,plain,(
% 1.34/0.90    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.34/0.90    inference(nnf_transformation,[],[f9])).
% 1.34/0.90  
% 1.34/0.90  fof(f22,plain,(
% 1.34/0.90    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.34/0.90    inference(rectify,[],[f21])).
% 1.34/0.90  
% 1.34/0.90  fof(f24,plain,(
% 1.34/0.90    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5)) & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1))))),
% 1.34/0.90    introduced(choice_axiom,[])).
% 1.34/0.90  
% 1.34/0.90  fof(f23,plain,(
% 1.34/0.90    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 1.34/0.90    introduced(choice_axiom,[])).
% 1.34/0.90  
% 1.34/0.90  fof(f25,plain,(
% 1.34/0.90    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK2(X0,X1,X2,X5)) & m1_subset_1(sK2(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.34/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f24,f23])).
% 1.34/0.90  
% 1.34/0.90  fof(f39,plain,(
% 1.34/0.90    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.34/0.90    inference(cnf_transformation,[],[f25])).
% 1.34/0.90  
% 1.34/0.90  fof(f5,axiom,(
% 1.34/0.90    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)))),
% 1.34/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.90  
% 1.34/0.90  fof(f12,plain,(
% 1.34/0.90    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.34/0.90    inference(ennf_transformation,[],[f5])).
% 1.34/0.90  
% 1.34/0.90  fof(f13,plain,(
% 1.34/0.90    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.34/0.90    inference(flattening,[],[f12])).
% 1.34/0.90  
% 1.34/0.90  fof(f44,plain,(
% 1.34/0.90    ( ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.34/0.90    inference(cnf_transformation,[],[f13])).
% 1.34/0.90  
% 1.34/0.90  fof(f49,plain,(
% 1.34/0.90    v7_waybel_0(sK4)),
% 1.34/0.90    inference(cnf_transformation,[],[f29])).
% 1.34/0.90  
% 1.34/0.90  fof(f48,plain,(
% 1.34/0.90    v4_orders_2(sK4)),
% 1.34/0.90    inference(cnf_transformation,[],[f29])).
% 1.34/0.90  
% 1.34/0.90  cnf(c_4,plain,
% 1.34/0.90      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
% 1.34/0.90      inference(cnf_transformation,[],[f59]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_3550,plain,
% 1.34/0.90      ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),X0)
% 1.34/0.90      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),k6_subset_1(X3,X0)) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_4]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_3552,plain,
% 1.34/0.90      ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),k6_subset_1(sK3,sK3))
% 1.34/0.90      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),sK3) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_3550]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_2,plain,
% 1.34/0.90      ( r2_hidden(sK0(X0,X1,X2),X0)
% 1.34/0.90      | r2_hidden(sK0(X0,X1,X2),X2)
% 1.34/0.90      | k6_subset_1(X0,X1) = X2 ),
% 1.34/0.90      inference(cnf_transformation,[],[f54]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_780,plain,
% 1.34/0.90      ( k6_subset_1(X0,X1) = X2
% 1.34/0.90      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 1.34/0.90      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 1.34/0.90      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1,plain,
% 1.34/0.90      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 1.34/0.90      | r2_hidden(sK0(X0,X1,X2),X2)
% 1.34/0.90      | k6_subset_1(X0,X1) = X2 ),
% 1.34/0.90      inference(cnf_transformation,[],[f53]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_781,plain,
% 1.34/0.90      ( k6_subset_1(X0,X1) = X2
% 1.34/0.90      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 1.34/0.90      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 1.34/0.90      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1365,plain,
% 1.34/0.90      ( k6_subset_1(X0,X0) = X1
% 1.34/0.90      | r2_hidden(sK0(X0,X0,X1),X1) = iProver_top ),
% 1.34/0.90      inference(superposition,[status(thm)],[c_780,c_781]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_5,plain,
% 1.34/0.90      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 1.34/0.90      inference(cnf_transformation,[],[f60]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_777,plain,
% 1.34/0.90      ( r2_hidden(X0,X1) = iProver_top
% 1.34/0.90      | r2_hidden(X0,k6_subset_1(X1,X2)) != iProver_top ),
% 1.34/0.90      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1667,plain,
% 1.34/0.90      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
% 1.34/0.90      | r2_hidden(sK0(X0,X0,k6_subset_1(X1,X2)),X1) = iProver_top ),
% 1.34/0.90      inference(superposition,[status(thm)],[c_1365,c_777]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_778,plain,
% 1.34/0.90      ( r2_hidden(X0,X1) != iProver_top
% 1.34/0.90      | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
% 1.34/0.90      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1668,plain,
% 1.34/0.90      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
% 1.34/0.90      | r2_hidden(sK0(X0,X0,k6_subset_1(X1,X2)),X2) != iProver_top ),
% 1.34/0.90      inference(superposition,[status(thm)],[c_1365,c_778]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_2171,plain,
% 1.34/0.90      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X1) ),
% 1.34/0.90      inference(superposition,[status(thm)],[c_1667,c_1668]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_11,plain,
% 1.34/0.90      ( r1_waybel_0(X0,X1,X2)
% 1.34/0.90      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 1.34/0.90      | ~ l1_waybel_0(X1,X0)
% 1.34/0.90      | ~ l1_struct_0(X0)
% 1.34/0.90      | v2_struct_0(X0)
% 1.34/0.90      | v2_struct_0(X1) ),
% 1.34/0.90      inference(cnf_transformation,[],[f43]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_14,negated_conjecture,
% 1.34/0.90      ( ~ r1_waybel_0(sK3,sK4,u1_struct_0(sK3)) ),
% 1.34/0.90      inference(cnf_transformation,[],[f51]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_309,plain,
% 1.34/0.90      ( r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 1.34/0.90      | ~ l1_waybel_0(X1,X0)
% 1.34/0.90      | ~ l1_struct_0(X0)
% 1.34/0.90      | v2_struct_0(X0)
% 1.34/0.90      | v2_struct_0(X1)
% 1.34/0.90      | u1_struct_0(sK3) != X2
% 1.34/0.90      | sK4 != X1
% 1.34/0.90      | sK3 != X0 ),
% 1.34/0.90      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_310,plain,
% 1.34/0.90      ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))
% 1.34/0.90      | ~ l1_waybel_0(sK4,sK3)
% 1.34/0.90      | ~ l1_struct_0(sK3)
% 1.34/0.90      | v2_struct_0(sK4)
% 1.34/0.90      | v2_struct_0(sK3) ),
% 1.34/0.90      inference(unflattening,[status(thm)],[c_309]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_20,negated_conjecture,
% 1.34/0.90      ( ~ v2_struct_0(sK3) ),
% 1.34/0.90      inference(cnf_transformation,[],[f45]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_19,negated_conjecture,
% 1.34/0.90      ( l1_struct_0(sK3) ),
% 1.34/0.90      inference(cnf_transformation,[],[f46]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_18,negated_conjecture,
% 1.34/0.90      ( ~ v2_struct_0(sK4) ),
% 1.34/0.90      inference(cnf_transformation,[],[f47]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_15,negated_conjecture,
% 1.34/0.90      ( l1_waybel_0(sK4,sK3) ),
% 1.34/0.90      inference(cnf_transformation,[],[f50]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_312,plain,
% 1.34/0.90      ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
% 1.34/0.90      inference(global_propositional_subsumption,
% 1.34/0.90                [status(thm)],
% 1.34/0.90                [c_310,c_20,c_19,c_18,c_15]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_767,plain,
% 1.34/0.90      ( r2_waybel_0(sK3,sK4,k6_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) = iProver_top ),
% 1.34/0.90      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_2345,plain,
% 1.34/0.90      ( r2_waybel_0(sK3,sK4,k6_subset_1(X0,X0)) = iProver_top ),
% 1.34/0.90      inference(superposition,[status(thm)],[c_2171,c_767]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_2366,plain,
% 1.34/0.90      ( r2_waybel_0(sK3,sK4,k6_subset_1(X0,X0)) ),
% 1.34/0.90      inference(predicate_to_equality_rev,[status(thm)],[c_2345]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_2368,plain,
% 1.34/0.90      ( r2_waybel_0(sK3,sK4,k6_subset_1(sK3,sK3)) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_2366]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1648,plain,
% 1.34/0.90      ( r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),X0)
% 1.34/0.90      | ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),k6_subset_1(X0,X1)) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_5]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1654,plain,
% 1.34/0.90      ( ~ r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),k6_subset_1(sK3,sK3))
% 1.34/0.90      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),sK3) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_1648]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_8,plain,
% 1.34/0.90      ( ~ r2_waybel_0(X0,X1,X2)
% 1.34/0.90      | ~ l1_waybel_0(X1,X0)
% 1.34/0.90      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.34/0.90      | r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
% 1.34/0.90      | ~ l1_struct_0(X0)
% 1.34/0.90      | v2_struct_0(X0)
% 1.34/0.90      | v2_struct_0(X1) ),
% 1.34/0.90      inference(cnf_transformation,[],[f39]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_952,plain,
% 1.34/0.90      ( ~ r2_waybel_0(sK3,sK4,X0)
% 1.34/0.90      | ~ l1_waybel_0(sK4,sK3)
% 1.34/0.90      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.34/0.90      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,X1)),X0)
% 1.34/0.90      | ~ l1_struct_0(sK3)
% 1.34/0.90      | v2_struct_0(sK4)
% 1.34/0.90      | v2_struct_0(sK3) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_8]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1015,plain,
% 1.34/0.90      ( ~ r2_waybel_0(sK3,sK4,X0)
% 1.34/0.90      | ~ l1_waybel_0(sK4,sK3)
% 1.34/0.90      | ~ m1_subset_1(o_2_2_yellow_6(X1,sK4),u1_struct_0(sK4))
% 1.34/0.90      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,X0,o_2_2_yellow_6(X1,sK4))),X0)
% 1.34/0.90      | ~ l1_struct_0(sK3)
% 1.34/0.90      | v2_struct_0(sK4)
% 1.34/0.90      | v2_struct_0(sK3) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_952]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1647,plain,
% 1.34/0.90      ( ~ r2_waybel_0(sK3,sK4,k6_subset_1(X0,X1))
% 1.34/0.90      | ~ l1_waybel_0(sK4,sK3)
% 1.34/0.90      | ~ m1_subset_1(o_2_2_yellow_6(X2,sK4),u1_struct_0(sK4))
% 1.34/0.90      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(X0,X1),o_2_2_yellow_6(X2,sK4))),k6_subset_1(X0,X1))
% 1.34/0.90      | ~ l1_struct_0(sK3)
% 1.34/0.90      | v2_struct_0(sK4)
% 1.34/0.90      | v2_struct_0(sK3) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_1015]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_1650,plain,
% 1.34/0.90      ( ~ r2_waybel_0(sK3,sK4,k6_subset_1(sK3,sK3))
% 1.34/0.90      | ~ l1_waybel_0(sK4,sK3)
% 1.34/0.90      | ~ m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4))
% 1.34/0.90      | r2_hidden(k2_waybel_0(sK3,sK4,sK2(sK3,sK4,k6_subset_1(sK3,sK3),o_2_2_yellow_6(sK3,sK4))),k6_subset_1(sK3,sK3))
% 1.34/0.90      | ~ l1_struct_0(sK3)
% 1.34/0.90      | v2_struct_0(sK4)
% 1.34/0.90      | v2_struct_0(sK3) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_1647]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_13,plain,
% 1.34/0.90      ( ~ l1_waybel_0(X0,X1)
% 1.34/0.90      | m1_subset_1(o_2_2_yellow_6(X1,X0),u1_struct_0(X0))
% 1.34/0.90      | ~ v4_orders_2(X0)
% 1.34/0.90      | ~ v7_waybel_0(X0)
% 1.34/0.90      | ~ l1_struct_0(X1)
% 1.34/0.90      | v2_struct_0(X1)
% 1.34/0.90      | v2_struct_0(X0) ),
% 1.34/0.90      inference(cnf_transformation,[],[f44]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_16,negated_conjecture,
% 1.34/0.90      ( v7_waybel_0(sK4) ),
% 1.34/0.90      inference(cnf_transformation,[],[f49]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_229,plain,
% 1.34/0.90      ( ~ l1_waybel_0(X0,X1)
% 1.34/0.90      | m1_subset_1(o_2_2_yellow_6(X1,X0),u1_struct_0(X0))
% 1.34/0.90      | ~ v4_orders_2(X0)
% 1.34/0.90      | ~ l1_struct_0(X1)
% 1.34/0.90      | v2_struct_0(X0)
% 1.34/0.90      | v2_struct_0(X1)
% 1.34/0.90      | sK4 != X0 ),
% 1.34/0.90      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_230,plain,
% 1.34/0.90      ( ~ l1_waybel_0(sK4,X0)
% 1.34/0.90      | m1_subset_1(o_2_2_yellow_6(X0,sK4),u1_struct_0(sK4))
% 1.34/0.90      | ~ v4_orders_2(sK4)
% 1.34/0.90      | ~ l1_struct_0(X0)
% 1.34/0.90      | v2_struct_0(X0)
% 1.34/0.90      | v2_struct_0(sK4) ),
% 1.34/0.90      inference(unflattening,[status(thm)],[c_229]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_232,plain,
% 1.34/0.90      ( ~ l1_waybel_0(sK4,sK3)
% 1.34/0.90      | m1_subset_1(o_2_2_yellow_6(sK3,sK4),u1_struct_0(sK4))
% 1.34/0.90      | ~ v4_orders_2(sK4)
% 1.34/0.90      | ~ l1_struct_0(sK3)
% 1.34/0.90      | v2_struct_0(sK4)
% 1.34/0.90      | v2_struct_0(sK3) ),
% 1.34/0.90      inference(instantiation,[status(thm)],[c_230]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(c_17,negated_conjecture,
% 1.34/0.90      ( v4_orders_2(sK4) ),
% 1.34/0.90      inference(cnf_transformation,[],[f48]) ).
% 1.34/0.90  
% 1.34/0.90  cnf(contradiction,plain,
% 1.34/0.90      ( $false ),
% 1.34/0.90      inference(minisat,
% 1.34/0.90                [status(thm)],
% 1.34/0.90                [c_3552,c_2368,c_1654,c_1650,c_232,c_15,c_17,c_18,c_19,
% 1.34/0.90                 c_20]) ).
% 1.34/0.90  
% 1.34/0.90  
% 1.34/0.90  % SZS output end CNFRefutation for theBenchmark.p
% 1.34/0.90  
% 1.34/0.90  ------                               Statistics
% 1.34/0.90  
% 1.34/0.90  ------ General
% 1.34/0.90  
% 1.34/0.90  abstr_ref_over_cycles:                  0
% 1.34/0.90  abstr_ref_under_cycles:                 0
% 1.34/0.90  gc_basic_clause_elim:                   0
% 1.34/0.90  forced_gc_time:                         0
% 1.34/0.90  parsing_time:                           0.009
% 1.34/0.90  unif_index_cands_time:                  0.
% 1.34/0.90  unif_index_add_time:                    0.
% 1.34/0.90  orderings_time:                         0.
% 1.34/0.90  out_proof_time:                         0.011
% 1.34/0.90  total_time:                             0.137
% 1.34/0.90  num_of_symbols:                         50
% 1.34/0.90  num_of_terms:                           4371
% 1.34/0.90  
% 1.34/0.90  ------ Preprocessing
% 1.34/0.90  
% 1.34/0.90  num_of_splits:                          0
% 1.34/0.90  num_of_split_atoms:                     0
% 1.34/0.90  num_of_reused_defs:                     0
% 1.34/0.90  num_eq_ax_congr_red:                    42
% 1.34/0.90  num_of_sem_filtered_clauses:            1
% 1.34/0.90  num_of_subtypes:                        0
% 1.34/0.90  monotx_restored_types:                  0
% 1.34/0.90  sat_num_of_epr_types:                   0
% 1.34/0.90  sat_num_of_non_cyclic_types:            0
% 1.34/0.90  sat_guarded_non_collapsed_types:        0
% 1.34/0.90  num_pure_diseq_elim:                    0
% 1.34/0.90  simp_replaced_by:                       0
% 1.34/0.90  res_preprocessed:                       96
% 1.34/0.90  prep_upred:                             0
% 1.34/0.90  prep_unflattend:                        7
% 1.34/0.90  smt_new_axioms:                         0
% 1.34/0.90  pred_elim_cands:                        6
% 1.34/0.90  pred_elim:                              4
% 1.34/0.90  pred_elim_cl:                           5
% 1.34/0.90  pred_elim_cycles:                       6
% 1.34/0.90  merged_defs:                            0
% 1.34/0.90  merged_defs_ncl:                        0
% 1.34/0.90  bin_hyper_res:                          0
% 1.34/0.90  prep_cycles:                            4
% 1.34/0.90  pred_elim_time:                         0.002
% 1.34/0.90  splitting_time:                         0.
% 1.34/0.90  sem_filter_time:                        0.
% 1.34/0.90  monotx_time:                            0.
% 1.34/0.90  subtype_inf_time:                       0.
% 1.34/0.90  
% 1.34/0.90  ------ Problem properties
% 1.34/0.90  
% 1.34/0.90  clauses:                                16
% 1.34/0.90  conjectures:                            4
% 1.34/0.90  epr:                                    4
% 1.34/0.90  horn:                                   7
% 1.34/0.90  ground:                                 5
% 1.34/0.90  unary:                                  5
% 1.34/0.90  binary:                                 2
% 1.34/0.90  lits:                                   56
% 1.34/0.90  lits_eq:                                3
% 1.34/0.90  fd_pure:                                0
% 1.34/0.90  fd_pseudo:                              0
% 1.34/0.90  fd_cond:                                0
% 1.34/0.90  fd_pseudo_cond:                         3
% 1.34/0.90  ac_symbols:                             0
% 1.34/0.90  
% 1.34/0.90  ------ Propositional Solver
% 1.34/0.90  
% 1.34/0.90  prop_solver_calls:                      26
% 1.34/0.90  prop_fast_solver_calls:                 776
% 1.34/0.90  smt_solver_calls:                       0
% 1.34/0.90  smt_fast_solver_calls:                  0
% 1.34/0.90  prop_num_of_clauses:                    1128
% 1.34/0.90  prop_preprocess_simplified:             4023
% 1.34/0.90  prop_fo_subsumed:                       6
% 1.34/0.90  prop_solver_time:                       0.
% 1.34/0.90  smt_solver_time:                        0.
% 1.34/0.90  smt_fast_solver_time:                   0.
% 1.34/0.90  prop_fast_solver_time:                  0.
% 1.34/0.90  prop_unsat_core_time:                   0.
% 1.34/0.90  
% 1.34/0.90  ------ QBF
% 1.34/0.90  
% 1.34/0.90  qbf_q_res:                              0
% 1.34/0.90  qbf_num_tautologies:                    0
% 1.34/0.90  qbf_prep_cycles:                        0
% 1.34/0.90  
% 1.34/0.90  ------ BMC1
% 1.34/0.90  
% 1.34/0.90  bmc1_current_bound:                     -1
% 1.34/0.90  bmc1_last_solved_bound:                 -1
% 1.34/0.90  bmc1_unsat_core_size:                   -1
% 1.34/0.90  bmc1_unsat_core_parents_size:           -1
% 1.34/0.90  bmc1_merge_next_fun:                    0
% 1.34/0.90  bmc1_unsat_core_clauses_time:           0.
% 1.34/0.90  
% 1.34/0.90  ------ Instantiation
% 1.34/0.90  
% 1.34/0.90  inst_num_of_clauses:                    299
% 1.34/0.90  inst_num_in_passive:                    101
% 1.34/0.90  inst_num_in_active:                     158
% 1.34/0.90  inst_num_in_unprocessed:                39
% 1.34/0.90  inst_num_of_loops:                      201
% 1.34/0.90  inst_num_of_learning_restarts:          0
% 1.34/0.90  inst_num_moves_active_passive:          38
% 1.34/0.90  inst_lit_activity:                      0
% 1.34/0.90  inst_lit_activity_moves:                0
% 1.34/0.90  inst_num_tautologies:                   0
% 1.34/0.90  inst_num_prop_implied:                  0
% 1.34/0.90  inst_num_existing_simplified:           0
% 1.34/0.90  inst_num_eq_res_simplified:             0
% 1.34/0.90  inst_num_child_elim:                    0
% 1.34/0.90  inst_num_of_dismatching_blockings:      26
% 1.34/0.90  inst_num_of_non_proper_insts:           220
% 1.34/0.90  inst_num_of_duplicates:                 0
% 1.34/0.90  inst_inst_num_from_inst_to_res:         0
% 1.34/0.90  inst_dismatching_checking_time:         0.
% 1.34/0.90  
% 1.34/0.90  ------ Resolution
% 1.34/0.90  
% 1.34/0.90  res_num_of_clauses:                     0
% 1.34/0.90  res_num_in_passive:                     0
% 1.34/0.90  res_num_in_active:                      0
% 1.34/0.90  res_num_of_loops:                       100
% 1.34/0.90  res_forward_subset_subsumed:            12
% 1.34/0.90  res_backward_subset_subsumed:           0
% 1.34/0.90  res_forward_subsumed:                   0
% 1.34/0.90  res_backward_subsumed:                  0
% 1.34/0.90  res_forward_subsumption_resolution:     2
% 1.34/0.90  res_backward_subsumption_resolution:    0
% 1.34/0.90  res_clause_to_clause_subsumption:       842
% 1.34/0.90  res_orphan_elimination:                 0
% 1.34/0.90  res_tautology_del:                      19
% 1.34/0.90  res_num_eq_res_simplified:              0
% 1.34/0.90  res_num_sel_changes:                    0
% 1.34/0.90  res_moves_from_active_to_pass:          0
% 1.34/0.90  
% 1.34/0.90  ------ Superposition
% 1.34/0.90  
% 1.34/0.90  sup_time_total:                         0.
% 1.34/0.90  sup_time_generating:                    0.
% 1.34/0.90  sup_time_sim_full:                      0.
% 1.34/0.90  sup_time_sim_immed:                     0.
% 1.34/0.90  
% 1.34/0.90  sup_num_of_clauses:                     86
% 1.34/0.90  sup_num_in_active:                      37
% 1.34/0.90  sup_num_in_passive:                     49
% 1.34/0.90  sup_num_of_loops:                       40
% 1.34/0.90  sup_fw_superposition:                   173
% 1.34/0.90  sup_bw_superposition:                   144
% 1.34/0.90  sup_immediate_simplified:               78
% 1.34/0.90  sup_given_eliminated:                   3
% 1.34/0.90  comparisons_done:                       0
% 1.34/0.90  comparisons_avoided:                    0
% 1.34/0.90  
% 1.34/0.90  ------ Simplifications
% 1.34/0.90  
% 1.34/0.90  
% 1.34/0.90  sim_fw_subset_subsumed:                 21
% 1.34/0.90  sim_bw_subset_subsumed:                 1
% 1.34/0.90  sim_fw_subsumed:                        38
% 1.34/0.90  sim_bw_subsumed:                        5
% 1.34/0.90  sim_fw_subsumption_res:                 3
% 1.34/0.90  sim_bw_subsumption_res:                 0
% 1.34/0.90  sim_tautology_del:                      19
% 1.34/0.90  sim_eq_tautology_del:                   9
% 1.34/0.90  sim_eq_res_simp:                        1
% 1.34/0.90  sim_fw_demodulated:                     27
% 1.34/0.90  sim_bw_demodulated:                     0
% 1.34/0.90  sim_light_normalised:                   3
% 1.34/0.90  sim_joinable_taut:                      0
% 1.34/0.90  sim_joinable_simp:                      0
% 1.34/0.90  sim_ac_normalised:                      0
% 1.34/0.90  sim_smt_subsumption:                    0
% 1.34/0.90  
%------------------------------------------------------------------------------
