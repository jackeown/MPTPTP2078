%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:07 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 174 expanded)
%              Number of clauses        :   30 (  34 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  366 (1194 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
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

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

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

fof(f8,plain,(
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

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
             => r2_waybel_0(X0,X1,X2) ) ) ) ),
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
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
               => r2_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
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
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_waybel_0(X0,X1,X2)
          & r1_waybel_0(X0,X1,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK4)
        & r1_waybel_0(X0,X1,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_waybel_0(X0,sK3,X2)
            & r1_waybel_0(X0,sK3,X2) )
        & l1_waybel_0(sK3,X0)
        & v7_waybel_0(sK3)
        & v4_orders_2(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_waybel_0(X0,X1,X2)
                & r1_waybel_0(X0,X1,X2) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(sK2,X1,X2)
              & r1_waybel_0(sK2,X1,X2) )
          & l1_waybel_0(X1,sK2)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_waybel_0(sK2,sK3,sK4)
    & r1_waybel_0(sK2,sK3,sK4)
    & l1_waybel_0(sK3,sK2)
    & v7_waybel_0(sK3)
    & v4_orders_2(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f26,f25,f24])).

fof(f46,plain,(
    l1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    v7_waybel_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ~ r2_waybel_0(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    r1_waybel_0(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1104,plain,
    ( ~ r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),k6_subset_1(X0,sK4))
    | ~ r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1244,plain,
    ( ~ r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),k6_subset_1(u1_struct_0(sK2),sK4))
    | ~ r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_943,plain,
    ( r1_xboole_0(k6_subset_1(u1_struct_0(sK2),sK4),sK4)
    | r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),k6_subset_1(u1_struct_0(sK2),sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_944,plain,
    ( r1_xboole_0(k6_subset_1(u1_struct_0(sK2),sK4),sK4)
    | r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_14,negated_conjecture,
    ( l1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( v7_waybel_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_212,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_xboole_0(X3,X2)
    | ~ v4_orders_2(X1)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_213,plain,
    ( ~ r1_waybel_0(X0,sK3,X1)
    | ~ r1_waybel_0(X0,sK3,X2)
    | ~ l1_waybel_0(sK3,X0)
    | ~ r1_xboole_0(X1,X2)
    | ~ v4_orders_2(sK3)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_217,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ r1_waybel_0(X0,sK3,X1)
    | ~ r1_waybel_0(X0,sK3,X2)
    | ~ l1_waybel_0(sK3,X0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_213,c_17,c_16])).

cnf(c_218,plain,
    ( ~ r1_waybel_0(X0,sK3,X1)
    | ~ r1_waybel_0(X0,sK3,X2)
    | ~ l1_waybel_0(sK3,X0)
    | ~ r1_xboole_0(X2,X1)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_263,plain,
    ( ~ r1_waybel_0(X0,sK3,X1)
    | ~ r1_waybel_0(X0,sK3,X2)
    | ~ r1_xboole_0(X1,X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | sK3 != sK3
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_218])).

cnf(c_264,plain,
    ( ~ r1_waybel_0(sK2,sK3,X0)
    | ~ r1_waybel_0(sK2,sK3,X1)
    | ~ r1_xboole_0(X1,X0)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_268,plain,
    ( ~ r1_waybel_0(sK2,sK3,X0)
    | ~ r1_waybel_0(sK2,sK3,X1)
    | ~ r1_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_19,c_18])).

cnf(c_269,plain,
    ( ~ r1_waybel_0(sK2,sK3,X0)
    | ~ r1_waybel_0(sK2,sK3,X1)
    | ~ r1_xboole_0(X0,X1) ),
    inference(renaming,[status(thm)],[c_268])).

cnf(c_811,plain,
    ( ~ r1_waybel_0(sK2,sK3,X0)
    | ~ r1_waybel_0(sK2,sK3,k6_subset_1(u1_struct_0(sK2),sK4))
    | ~ r1_xboole_0(k6_subset_1(u1_struct_0(sK2),sK4),X0) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_893,plain,
    ( ~ r1_waybel_0(sK2,sK3,k6_subset_1(u1_struct_0(sK2),sK4))
    | ~ r1_waybel_0(sK2,sK3,sK4)
    | ~ r1_xboole_0(k6_subset_1(u1_struct_0(sK2),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_9,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,negated_conjecture,
    ( ~ r2_waybel_0(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_250,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK4 != X2
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_251,plain,
    ( r1_waybel_0(sK2,sK3,k6_subset_1(u1_struct_0(sK2),sK4))
    | ~ l1_waybel_0(sK3,sK2)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_13,negated_conjecture,
    ( r1_waybel_0(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1244,c_943,c_944,c_893,c_251,c_13,c_14,c_17,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.82/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.82/1.04  
% 0.82/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.82/1.04  
% 0.82/1.04  ------  iProver source info
% 0.82/1.04  
% 0.82/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.82/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.82/1.04  git: non_committed_changes: false
% 0.82/1.04  git: last_make_outside_of_git: false
% 0.82/1.04  
% 0.82/1.04  ------ 
% 0.82/1.04  
% 0.82/1.04  ------ Input Options
% 0.82/1.04  
% 0.82/1.04  --out_options                           all
% 0.82/1.04  --tptp_safe_out                         true
% 0.82/1.04  --problem_path                          ""
% 0.82/1.04  --include_path                          ""
% 0.82/1.04  --clausifier                            res/vclausify_rel
% 0.82/1.04  --clausifier_options                    --mode clausify
% 0.82/1.04  --stdin                                 false
% 0.82/1.04  --stats_out                             all
% 0.82/1.04  
% 0.82/1.04  ------ General Options
% 0.82/1.04  
% 0.82/1.04  --fof                                   false
% 0.82/1.04  --time_out_real                         305.
% 0.82/1.04  --time_out_virtual                      -1.
% 0.82/1.04  --symbol_type_check                     false
% 0.82/1.04  --clausify_out                          false
% 0.82/1.04  --sig_cnt_out                           false
% 0.82/1.04  --trig_cnt_out                          false
% 0.82/1.04  --trig_cnt_out_tolerance                1.
% 0.82/1.04  --trig_cnt_out_sk_spl                   false
% 0.82/1.04  --abstr_cl_out                          false
% 0.82/1.04  
% 0.82/1.04  ------ Global Options
% 0.82/1.04  
% 0.82/1.04  --schedule                              default
% 0.82/1.04  --add_important_lit                     false
% 0.82/1.04  --prop_solver_per_cl                    1000
% 0.82/1.04  --min_unsat_core                        false
% 0.82/1.04  --soft_assumptions                      false
% 0.82/1.04  --soft_lemma_size                       3
% 0.82/1.04  --prop_impl_unit_size                   0
% 0.82/1.04  --prop_impl_unit                        []
% 0.82/1.04  --share_sel_clauses                     true
% 0.82/1.04  --reset_solvers                         false
% 0.82/1.04  --bc_imp_inh                            [conj_cone]
% 0.82/1.04  --conj_cone_tolerance                   3.
% 0.82/1.04  --extra_neg_conj                        none
% 0.82/1.04  --large_theory_mode                     true
% 0.82/1.04  --prolific_symb_bound                   200
% 0.82/1.04  --lt_threshold                          2000
% 0.82/1.04  --clause_weak_htbl                      true
% 0.82/1.04  --gc_record_bc_elim                     false
% 0.82/1.04  
% 0.82/1.04  ------ Preprocessing Options
% 0.82/1.04  
% 0.82/1.04  --preprocessing_flag                    true
% 0.82/1.04  --time_out_prep_mult                    0.1
% 0.82/1.04  --splitting_mode                        input
% 0.82/1.04  --splitting_grd                         true
% 0.82/1.04  --splitting_cvd                         false
% 0.82/1.04  --splitting_cvd_svl                     false
% 0.82/1.04  --splitting_nvd                         32
% 0.82/1.04  --sub_typing                            true
% 0.82/1.04  --prep_gs_sim                           true
% 0.82/1.04  --prep_unflatten                        true
% 0.82/1.04  --prep_res_sim                          true
% 0.82/1.04  --prep_upred                            true
% 0.82/1.04  --prep_sem_filter                       exhaustive
% 0.82/1.04  --prep_sem_filter_out                   false
% 0.82/1.04  --pred_elim                             true
% 0.82/1.04  --res_sim_input                         true
% 0.82/1.04  --eq_ax_congr_red                       true
% 0.82/1.04  --pure_diseq_elim                       true
% 0.82/1.04  --brand_transform                       false
% 0.82/1.04  --non_eq_to_eq                          false
% 0.82/1.04  --prep_def_merge                        true
% 0.82/1.04  --prep_def_merge_prop_impl              false
% 0.82/1.04  --prep_def_merge_mbd                    true
% 0.82/1.04  --prep_def_merge_tr_red                 false
% 0.82/1.04  --prep_def_merge_tr_cl                  false
% 0.82/1.04  --smt_preprocessing                     true
% 0.82/1.04  --smt_ac_axioms                         fast
% 0.82/1.04  --preprocessed_out                      false
% 0.82/1.04  --preprocessed_stats                    false
% 0.82/1.04  
% 0.82/1.04  ------ Abstraction refinement Options
% 0.82/1.04  
% 0.82/1.04  --abstr_ref                             []
% 0.82/1.04  --abstr_ref_prep                        false
% 0.82/1.04  --abstr_ref_until_sat                   false
% 0.82/1.04  --abstr_ref_sig_restrict                funpre
% 0.82/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/1.04  --abstr_ref_under                       []
% 0.82/1.04  
% 0.82/1.04  ------ SAT Options
% 0.82/1.04  
% 0.82/1.04  --sat_mode                              false
% 0.82/1.04  --sat_fm_restart_options                ""
% 0.82/1.04  --sat_gr_def                            false
% 0.82/1.04  --sat_epr_types                         true
% 0.82/1.04  --sat_non_cyclic_types                  false
% 0.82/1.04  --sat_finite_models                     false
% 0.82/1.04  --sat_fm_lemmas                         false
% 0.82/1.04  --sat_fm_prep                           false
% 0.82/1.04  --sat_fm_uc_incr                        true
% 0.82/1.04  --sat_out_model                         small
% 0.82/1.04  --sat_out_clauses                       false
% 0.82/1.04  
% 0.82/1.04  ------ QBF Options
% 0.82/1.04  
% 0.82/1.04  --qbf_mode                              false
% 0.82/1.04  --qbf_elim_univ                         false
% 0.82/1.04  --qbf_dom_inst                          none
% 0.82/1.04  --qbf_dom_pre_inst                      false
% 0.82/1.04  --qbf_sk_in                             false
% 0.82/1.04  --qbf_pred_elim                         true
% 0.82/1.04  --qbf_split                             512
% 0.82/1.04  
% 0.82/1.04  ------ BMC1 Options
% 0.82/1.04  
% 0.82/1.04  --bmc1_incremental                      false
% 0.82/1.04  --bmc1_axioms                           reachable_all
% 0.82/1.04  --bmc1_min_bound                        0
% 0.82/1.04  --bmc1_max_bound                        -1
% 0.82/1.04  --bmc1_max_bound_default                -1
% 0.82/1.04  --bmc1_symbol_reachability              true
% 0.82/1.04  --bmc1_property_lemmas                  false
% 0.82/1.04  --bmc1_k_induction                      false
% 0.82/1.04  --bmc1_non_equiv_states                 false
% 0.82/1.04  --bmc1_deadlock                         false
% 0.82/1.04  --bmc1_ucm                              false
% 0.82/1.04  --bmc1_add_unsat_core                   none
% 0.82/1.04  --bmc1_unsat_core_children              false
% 0.82/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/1.04  --bmc1_out_stat                         full
% 0.82/1.04  --bmc1_ground_init                      false
% 0.82/1.04  --bmc1_pre_inst_next_state              false
% 0.82/1.04  --bmc1_pre_inst_state                   false
% 0.82/1.04  --bmc1_pre_inst_reach_state             false
% 0.82/1.04  --bmc1_out_unsat_core                   false
% 0.82/1.04  --bmc1_aig_witness_out                  false
% 0.82/1.04  --bmc1_verbose                          false
% 0.82/1.04  --bmc1_dump_clauses_tptp                false
% 0.82/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.82/1.04  --bmc1_dump_file                        -
% 0.82/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.82/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.82/1.04  --bmc1_ucm_extend_mode                  1
% 0.82/1.04  --bmc1_ucm_init_mode                    2
% 0.82/1.04  --bmc1_ucm_cone_mode                    none
% 0.82/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.82/1.04  --bmc1_ucm_relax_model                  4
% 0.82/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.82/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/1.04  --bmc1_ucm_layered_model                none
% 0.82/1.04  --bmc1_ucm_max_lemma_size               10
% 0.82/1.04  
% 0.82/1.04  ------ AIG Options
% 0.82/1.04  
% 0.82/1.04  --aig_mode                              false
% 0.82/1.04  
% 0.82/1.04  ------ Instantiation Options
% 0.82/1.04  
% 0.82/1.04  --instantiation_flag                    true
% 0.82/1.04  --inst_sos_flag                         false
% 0.82/1.04  --inst_sos_phase                        true
% 0.82/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/1.04  --inst_lit_sel_side                     num_symb
% 0.82/1.04  --inst_solver_per_active                1400
% 0.82/1.04  --inst_solver_calls_frac                1.
% 0.82/1.04  --inst_passive_queue_type               priority_queues
% 0.82/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/1.04  --inst_passive_queues_freq              [25;2]
% 0.82/1.04  --inst_dismatching                      true
% 0.82/1.04  --inst_eager_unprocessed_to_passive     true
% 0.82/1.04  --inst_prop_sim_given                   true
% 0.82/1.04  --inst_prop_sim_new                     false
% 0.82/1.04  --inst_subs_new                         false
% 0.82/1.04  --inst_eq_res_simp                      false
% 0.82/1.04  --inst_subs_given                       false
% 0.82/1.04  --inst_orphan_elimination               true
% 0.82/1.04  --inst_learning_loop_flag               true
% 0.82/1.04  --inst_learning_start                   3000
% 0.82/1.04  --inst_learning_factor                  2
% 0.82/1.04  --inst_start_prop_sim_after_learn       3
% 0.82/1.04  --inst_sel_renew                        solver
% 0.82/1.04  --inst_lit_activity_flag                true
% 0.82/1.04  --inst_restr_to_given                   false
% 0.82/1.04  --inst_activity_threshold               500
% 0.82/1.04  --inst_out_proof                        true
% 0.82/1.04  
% 0.82/1.04  ------ Resolution Options
% 0.82/1.04  
% 0.82/1.04  --resolution_flag                       true
% 0.82/1.04  --res_lit_sel                           adaptive
% 0.82/1.04  --res_lit_sel_side                      none
% 0.82/1.04  --res_ordering                          kbo
% 0.82/1.04  --res_to_prop_solver                    active
% 0.82/1.04  --res_prop_simpl_new                    false
% 0.82/1.04  --res_prop_simpl_given                  true
% 0.82/1.04  --res_passive_queue_type                priority_queues
% 0.82/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/1.04  --res_passive_queues_freq               [15;5]
% 0.82/1.04  --res_forward_subs                      full
% 0.82/1.04  --res_backward_subs                     full
% 0.82/1.04  --res_forward_subs_resolution           true
% 0.82/1.04  --res_backward_subs_resolution          true
% 0.82/1.04  --res_orphan_elimination                true
% 0.82/1.04  --res_time_limit                        2.
% 0.82/1.04  --res_out_proof                         true
% 0.82/1.04  
% 0.82/1.04  ------ Superposition Options
% 0.82/1.04  
% 0.82/1.04  --superposition_flag                    true
% 0.82/1.04  --sup_passive_queue_type                priority_queues
% 0.82/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.82/1.04  --demod_completeness_check              fast
% 0.82/1.04  --demod_use_ground                      true
% 0.82/1.04  --sup_to_prop_solver                    passive
% 0.82/1.04  --sup_prop_simpl_new                    true
% 0.82/1.04  --sup_prop_simpl_given                  true
% 0.82/1.04  --sup_fun_splitting                     false
% 0.82/1.04  --sup_smt_interval                      50000
% 0.82/1.04  
% 0.82/1.04  ------ Superposition Simplification Setup
% 0.82/1.04  
% 0.82/1.04  --sup_indices_passive                   []
% 0.82/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.04  --sup_full_bw                           [BwDemod]
% 0.82/1.04  --sup_immed_triv                        [TrivRules]
% 0.82/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.04  --sup_immed_bw_main                     []
% 0.82/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/1.04  
% 0.82/1.04  ------ Combination Options
% 0.82/1.04  
% 0.82/1.04  --comb_res_mult                         3
% 0.82/1.04  --comb_sup_mult                         2
% 0.82/1.04  --comb_inst_mult                        10
% 0.82/1.04  
% 0.82/1.04  ------ Debug Options
% 0.82/1.04  
% 0.82/1.04  --dbg_backtrace                         false
% 0.82/1.04  --dbg_dump_prop_clauses                 false
% 0.82/1.04  --dbg_dump_prop_clauses_file            -
% 0.82/1.04  --dbg_out_stat                          false
% 0.82/1.04  ------ Parsing...
% 0.82/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.82/1.04  
% 0.82/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.82/1.04  
% 0.82/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.82/1.04  
% 0.82/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.82/1.04  ------ Proving...
% 0.82/1.04  ------ Problem Properties 
% 0.82/1.04  
% 0.82/1.04  
% 0.82/1.04  clauses                                 12
% 0.82/1.04  conjectures                             1
% 0.82/1.04  EPR                                     3
% 0.82/1.04  Horn                                    6
% 0.82/1.04  unary                                   2
% 0.82/1.04  binary                                  4
% 0.82/1.04  lits                                    29
% 0.82/1.04  lits eq                                 3
% 0.82/1.04  fd_pure                                 0
% 0.82/1.04  fd_pseudo                               0
% 0.82/1.04  fd_cond                                 0
% 0.82/1.04  fd_pseudo_cond                          3
% 0.82/1.04  AC symbols                              0
% 0.82/1.04  
% 0.82/1.04  ------ Schedule dynamic 5 is on 
% 0.82/1.04  
% 0.82/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.82/1.04  
% 0.82/1.04  
% 0.82/1.04  ------ 
% 0.82/1.04  Current options:
% 0.82/1.04  ------ 
% 0.82/1.04  
% 0.82/1.04  ------ Input Options
% 0.82/1.04  
% 0.82/1.04  --out_options                           all
% 0.82/1.04  --tptp_safe_out                         true
% 0.82/1.04  --problem_path                          ""
% 0.82/1.04  --include_path                          ""
% 0.82/1.04  --clausifier                            res/vclausify_rel
% 0.82/1.04  --clausifier_options                    --mode clausify
% 0.82/1.04  --stdin                                 false
% 0.82/1.04  --stats_out                             all
% 0.82/1.04  
% 0.82/1.04  ------ General Options
% 0.82/1.04  
% 0.82/1.04  --fof                                   false
% 0.82/1.04  --time_out_real                         305.
% 0.82/1.04  --time_out_virtual                      -1.
% 0.82/1.04  --symbol_type_check                     false
% 0.82/1.04  --clausify_out                          false
% 0.82/1.04  --sig_cnt_out                           false
% 0.82/1.04  --trig_cnt_out                          false
% 0.82/1.04  --trig_cnt_out_tolerance                1.
% 0.82/1.04  --trig_cnt_out_sk_spl                   false
% 0.82/1.04  --abstr_cl_out                          false
% 0.82/1.04  
% 0.82/1.04  ------ Global Options
% 0.82/1.04  
% 0.82/1.04  --schedule                              default
% 0.82/1.04  --add_important_lit                     false
% 0.82/1.04  --prop_solver_per_cl                    1000
% 0.82/1.04  --min_unsat_core                        false
% 0.82/1.04  --soft_assumptions                      false
% 0.82/1.04  --soft_lemma_size                       3
% 0.82/1.04  --prop_impl_unit_size                   0
% 0.82/1.04  --prop_impl_unit                        []
% 0.82/1.04  --share_sel_clauses                     true
% 0.82/1.04  --reset_solvers                         false
% 0.82/1.04  --bc_imp_inh                            [conj_cone]
% 0.82/1.04  --conj_cone_tolerance                   3.
% 0.82/1.04  --extra_neg_conj                        none
% 0.82/1.04  --large_theory_mode                     true
% 0.82/1.04  --prolific_symb_bound                   200
% 0.82/1.04  --lt_threshold                          2000
% 0.82/1.04  --clause_weak_htbl                      true
% 0.82/1.04  --gc_record_bc_elim                     false
% 0.82/1.04  
% 0.82/1.04  ------ Preprocessing Options
% 0.82/1.04  
% 0.82/1.04  --preprocessing_flag                    true
% 0.82/1.04  --time_out_prep_mult                    0.1
% 0.82/1.04  --splitting_mode                        input
% 0.82/1.04  --splitting_grd                         true
% 0.82/1.04  --splitting_cvd                         false
% 0.82/1.04  --splitting_cvd_svl                     false
% 0.82/1.04  --splitting_nvd                         32
% 0.82/1.04  --sub_typing                            true
% 0.82/1.04  --prep_gs_sim                           true
% 0.82/1.04  --prep_unflatten                        true
% 0.82/1.04  --prep_res_sim                          true
% 0.82/1.04  --prep_upred                            true
% 0.82/1.04  --prep_sem_filter                       exhaustive
% 0.82/1.04  --prep_sem_filter_out                   false
% 0.82/1.04  --pred_elim                             true
% 0.82/1.04  --res_sim_input                         true
% 0.82/1.04  --eq_ax_congr_red                       true
% 0.82/1.04  --pure_diseq_elim                       true
% 0.82/1.04  --brand_transform                       false
% 0.82/1.04  --non_eq_to_eq                          false
% 0.82/1.04  --prep_def_merge                        true
% 0.82/1.04  --prep_def_merge_prop_impl              false
% 0.82/1.04  --prep_def_merge_mbd                    true
% 0.82/1.04  --prep_def_merge_tr_red                 false
% 0.82/1.04  --prep_def_merge_tr_cl                  false
% 0.82/1.04  --smt_preprocessing                     true
% 0.82/1.04  --smt_ac_axioms                         fast
% 0.82/1.04  --preprocessed_out                      false
% 0.82/1.04  --preprocessed_stats                    false
% 0.82/1.04  
% 0.82/1.04  ------ Abstraction refinement Options
% 0.82/1.04  
% 0.82/1.04  --abstr_ref                             []
% 0.82/1.04  --abstr_ref_prep                        false
% 0.82/1.04  --abstr_ref_until_sat                   false
% 0.82/1.04  --abstr_ref_sig_restrict                funpre
% 0.82/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/1.04  --abstr_ref_under                       []
% 0.82/1.04  
% 0.82/1.04  ------ SAT Options
% 0.82/1.04  
% 0.82/1.04  --sat_mode                              false
% 0.82/1.04  --sat_fm_restart_options                ""
% 0.82/1.04  --sat_gr_def                            false
% 0.82/1.04  --sat_epr_types                         true
% 0.82/1.04  --sat_non_cyclic_types                  false
% 0.82/1.04  --sat_finite_models                     false
% 0.82/1.04  --sat_fm_lemmas                         false
% 0.82/1.04  --sat_fm_prep                           false
% 0.82/1.04  --sat_fm_uc_incr                        true
% 0.82/1.04  --sat_out_model                         small
% 0.82/1.04  --sat_out_clauses                       false
% 0.82/1.04  
% 0.82/1.04  ------ QBF Options
% 0.82/1.04  
% 0.82/1.04  --qbf_mode                              false
% 0.82/1.04  --qbf_elim_univ                         false
% 0.82/1.04  --qbf_dom_inst                          none
% 0.82/1.04  --qbf_dom_pre_inst                      false
% 0.82/1.04  --qbf_sk_in                             false
% 0.82/1.04  --qbf_pred_elim                         true
% 0.82/1.04  --qbf_split                             512
% 0.82/1.04  
% 0.82/1.04  ------ BMC1 Options
% 0.82/1.04  
% 0.82/1.04  --bmc1_incremental                      false
% 0.82/1.04  --bmc1_axioms                           reachable_all
% 0.82/1.04  --bmc1_min_bound                        0
% 0.82/1.04  --bmc1_max_bound                        -1
% 0.82/1.04  --bmc1_max_bound_default                -1
% 0.82/1.04  --bmc1_symbol_reachability              true
% 0.82/1.04  --bmc1_property_lemmas                  false
% 0.82/1.04  --bmc1_k_induction                      false
% 0.82/1.04  --bmc1_non_equiv_states                 false
% 0.82/1.04  --bmc1_deadlock                         false
% 0.82/1.04  --bmc1_ucm                              false
% 0.82/1.04  --bmc1_add_unsat_core                   none
% 0.82/1.04  --bmc1_unsat_core_children              false
% 0.82/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/1.04  --bmc1_out_stat                         full
% 0.82/1.04  --bmc1_ground_init                      false
% 0.82/1.04  --bmc1_pre_inst_next_state              false
% 0.82/1.04  --bmc1_pre_inst_state                   false
% 0.82/1.04  --bmc1_pre_inst_reach_state             false
% 0.82/1.04  --bmc1_out_unsat_core                   false
% 0.82/1.04  --bmc1_aig_witness_out                  false
% 0.82/1.04  --bmc1_verbose                          false
% 0.82/1.04  --bmc1_dump_clauses_tptp                false
% 0.82/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.82/1.04  --bmc1_dump_file                        -
% 0.82/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.82/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.82/1.04  --bmc1_ucm_extend_mode                  1
% 0.82/1.04  --bmc1_ucm_init_mode                    2
% 0.82/1.04  --bmc1_ucm_cone_mode                    none
% 0.82/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.82/1.04  --bmc1_ucm_relax_model                  4
% 0.82/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.82/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/1.04  --bmc1_ucm_layered_model                none
% 0.82/1.04  --bmc1_ucm_max_lemma_size               10
% 0.82/1.04  
% 0.82/1.04  ------ AIG Options
% 0.82/1.04  
% 0.82/1.04  --aig_mode                              false
% 0.82/1.04  
% 0.82/1.04  ------ Instantiation Options
% 0.82/1.04  
% 0.82/1.04  --instantiation_flag                    true
% 0.82/1.04  --inst_sos_flag                         false
% 0.82/1.04  --inst_sos_phase                        true
% 0.82/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/1.04  --inst_lit_sel_side                     none
% 0.82/1.04  --inst_solver_per_active                1400
% 0.82/1.04  --inst_solver_calls_frac                1.
% 0.82/1.04  --inst_passive_queue_type               priority_queues
% 0.82/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/1.04  --inst_passive_queues_freq              [25;2]
% 0.82/1.04  --inst_dismatching                      true
% 0.82/1.04  --inst_eager_unprocessed_to_passive     true
% 0.82/1.04  --inst_prop_sim_given                   true
% 0.82/1.04  --inst_prop_sim_new                     false
% 0.82/1.04  --inst_subs_new                         false
% 0.82/1.04  --inst_eq_res_simp                      false
% 0.82/1.04  --inst_subs_given                       false
% 0.82/1.04  --inst_orphan_elimination               true
% 0.82/1.04  --inst_learning_loop_flag               true
% 0.82/1.04  --inst_learning_start                   3000
% 0.82/1.04  --inst_learning_factor                  2
% 0.82/1.04  --inst_start_prop_sim_after_learn       3
% 0.82/1.04  --inst_sel_renew                        solver
% 0.82/1.04  --inst_lit_activity_flag                true
% 0.82/1.04  --inst_restr_to_given                   false
% 0.82/1.04  --inst_activity_threshold               500
% 0.82/1.04  --inst_out_proof                        true
% 0.82/1.04  
% 0.82/1.04  ------ Resolution Options
% 0.82/1.04  
% 0.82/1.04  --resolution_flag                       false
% 0.82/1.04  --res_lit_sel                           adaptive
% 0.82/1.04  --res_lit_sel_side                      none
% 0.82/1.04  --res_ordering                          kbo
% 0.82/1.04  --res_to_prop_solver                    active
% 0.82/1.04  --res_prop_simpl_new                    false
% 0.82/1.04  --res_prop_simpl_given                  true
% 0.82/1.04  --res_passive_queue_type                priority_queues
% 0.82/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/1.04  --res_passive_queues_freq               [15;5]
% 0.82/1.04  --res_forward_subs                      full
% 0.82/1.04  --res_backward_subs                     full
% 0.82/1.04  --res_forward_subs_resolution           true
% 0.82/1.04  --res_backward_subs_resolution          true
% 0.82/1.04  --res_orphan_elimination                true
% 0.82/1.04  --res_time_limit                        2.
% 0.82/1.04  --res_out_proof                         true
% 0.82/1.04  
% 0.82/1.04  ------ Superposition Options
% 0.82/1.04  
% 0.82/1.04  --superposition_flag                    true
% 0.82/1.04  --sup_passive_queue_type                priority_queues
% 0.82/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.82/1.04  --demod_completeness_check              fast
% 0.82/1.04  --demod_use_ground                      true
% 0.82/1.04  --sup_to_prop_solver                    passive
% 0.82/1.04  --sup_prop_simpl_new                    true
% 0.82/1.04  --sup_prop_simpl_given                  true
% 0.82/1.04  --sup_fun_splitting                     false
% 0.82/1.04  --sup_smt_interval                      50000
% 0.82/1.04  
% 0.82/1.04  ------ Superposition Simplification Setup
% 0.82/1.04  
% 0.82/1.04  --sup_indices_passive                   []
% 0.82/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.04  --sup_full_bw                           [BwDemod]
% 0.82/1.04  --sup_immed_triv                        [TrivRules]
% 0.82/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.04  --sup_immed_bw_main                     []
% 0.82/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/1.04  
% 0.82/1.04  ------ Combination Options
% 0.82/1.04  
% 0.82/1.04  --comb_res_mult                         3
% 0.82/1.04  --comb_sup_mult                         2
% 0.82/1.04  --comb_inst_mult                        10
% 0.82/1.04  
% 0.82/1.04  ------ Debug Options
% 0.82/1.04  
% 0.82/1.04  --dbg_backtrace                         false
% 0.82/1.04  --dbg_dump_prop_clauses                 false
% 0.82/1.04  --dbg_dump_prop_clauses_file            -
% 0.82/1.04  --dbg_out_stat                          false
% 0.82/1.04  
% 0.82/1.04  
% 0.82/1.04  
% 0.82/1.04  
% 0.82/1.04  ------ Proving...
% 0.82/1.04  
% 0.82/1.04  
% 0.82/1.04  % SZS status Theorem for theBenchmark.p
% 0.82/1.04  
% 0.82/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.82/1.04  
% 0.82/1.04  fof(f1,axiom,(
% 0.82/1.04    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.82/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.04  
% 0.82/1.04  fof(f16,plain,(
% 0.82/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.82/1.04    inference(nnf_transformation,[],[f1])).
% 0.82/1.04  
% 0.82/1.04  fof(f17,plain,(
% 0.82/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.82/1.04    inference(flattening,[],[f16])).
% 0.82/1.04  
% 0.82/1.04  fof(f18,plain,(
% 0.82/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.82/1.04    inference(rectify,[],[f17])).
% 0.82/1.04  
% 0.82/1.04  fof(f19,plain,(
% 0.82/1.04    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 0.82/1.04    introduced(choice_axiom,[])).
% 0.82/1.04  
% 0.82/1.04  fof(f20,plain,(
% 0.82/1.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.82/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 0.82/1.04  
% 0.82/1.04  fof(f29,plain,(
% 0.82/1.04    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.82/1.04    inference(cnf_transformation,[],[f20])).
% 0.82/1.04  
% 0.82/1.04  fof(f3,axiom,(
% 0.82/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.82/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.04  
% 0.82/1.04  fof(f37,plain,(
% 0.82/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.82/1.04    inference(cnf_transformation,[],[f3])).
% 0.82/1.04  
% 0.82/1.04  fof(f53,plain,(
% 0.82/1.04    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.82/1.04    inference(definition_unfolding,[],[f29,f37])).
% 0.82/1.04  
% 0.82/1.04  fof(f56,plain,(
% 0.82/1.04    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 0.82/1.04    inference(equality_resolution,[],[f53])).
% 0.82/1.04  
% 0.82/1.04  fof(f2,axiom,(
% 0.82/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.82/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.04  
% 0.82/1.04  fof(f8,plain,(
% 0.82/1.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.82/1.04    inference(rectify,[],[f2])).
% 0.82/1.04  
% 0.82/1.04  fof(f9,plain,(
% 0.82/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.82/1.04    inference(ennf_transformation,[],[f8])).
% 0.82/1.04  
% 0.82/1.04  fof(f21,plain,(
% 0.82/1.04    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.82/1.04    introduced(choice_axiom,[])).
% 0.82/1.04  
% 0.82/1.04  fof(f22,plain,(
% 0.82/1.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.82/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f21])).
% 0.82/1.04  
% 0.82/1.04  fof(f34,plain,(
% 0.82/1.04    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.82/1.04    inference(cnf_transformation,[],[f22])).
% 0.82/1.04  
% 0.82/1.04  fof(f35,plain,(
% 0.82/1.04    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.82/1.04    inference(cnf_transformation,[],[f22])).
% 0.82/1.04  
% 0.82/1.04  fof(f6,conjecture,(
% 0.82/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 0.82/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.04  
% 0.82/1.04  fof(f7,negated_conjecture,(
% 0.82/1.04    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 0.82/1.04    inference(negated_conjecture,[],[f6])).
% 0.82/1.04  
% 0.82/1.04  fof(f14,plain,(
% 0.82/1.04    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.82/1.04    inference(ennf_transformation,[],[f7])).
% 0.82/1.04  
% 0.82/1.04  fof(f15,plain,(
% 0.82/1.04    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.82/1.04    inference(flattening,[],[f14])).
% 0.82/1.04  
% 0.82/1.04  fof(f26,plain,(
% 0.82/1.04    ( ! [X0,X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) => (~r2_waybel_0(X0,X1,sK4) & r1_waybel_0(X0,X1,sK4))) )),
% 0.82/1.04    introduced(choice_axiom,[])).
% 0.82/1.04  
% 0.82/1.04  fof(f25,plain,(
% 0.82/1.04    ( ! [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_waybel_0(X0,sK3,X2) & r1_waybel_0(X0,sK3,X2)) & l1_waybel_0(sK3,X0) & v7_waybel_0(sK3) & v4_orders_2(sK3) & ~v2_struct_0(sK3))) )),
% 0.82/1.04    introduced(choice_axiom,[])).
% 0.82/1.04  
% 0.82/1.04  fof(f24,plain,(
% 0.82/1.04    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_waybel_0(sK2,X1,X2) & r1_waybel_0(sK2,X1,X2)) & l1_waybel_0(X1,sK2) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.82/1.04    introduced(choice_axiom,[])).
% 0.82/1.04  
% 0.82/1.04  fof(f27,plain,(
% 0.82/1.04    ((~r2_waybel_0(sK2,sK3,sK4) & r1_waybel_0(sK2,sK3,sK4)) & l1_waybel_0(sK3,sK2) & v7_waybel_0(sK3) & v4_orders_2(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)),
% 0.82/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f26,f25,f24])).
% 0.82/1.04  
% 0.82/1.04  fof(f46,plain,(
% 0.82/1.04    l1_waybel_0(sK3,sK2)),
% 0.82/1.04    inference(cnf_transformation,[],[f27])).
% 0.82/1.04  
% 0.82/1.04  fof(f5,axiom,(
% 0.82/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 0.82/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.04  
% 0.82/1.04  fof(f12,plain,(
% 0.82/1.04    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.82/1.04    inference(ennf_transformation,[],[f5])).
% 0.82/1.04  
% 0.82/1.04  fof(f13,plain,(
% 0.82/1.04    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.82/1.04    inference(flattening,[],[f12])).
% 0.82/1.04  
% 0.82/1.04  fof(f40,plain,(
% 0.82/1.04    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.82/1.04    inference(cnf_transformation,[],[f13])).
% 0.82/1.04  
% 0.82/1.04  fof(f45,plain,(
% 0.82/1.04    v7_waybel_0(sK3)),
% 0.82/1.04    inference(cnf_transformation,[],[f27])).
% 0.82/1.04  
% 0.82/1.04  fof(f43,plain,(
% 0.82/1.04    ~v2_struct_0(sK3)),
% 0.82/1.04    inference(cnf_transformation,[],[f27])).
% 0.82/1.04  
% 0.82/1.04  fof(f44,plain,(
% 0.82/1.04    v4_orders_2(sK3)),
% 0.82/1.04    inference(cnf_transformation,[],[f27])).
% 0.82/1.04  
% 0.82/1.04  fof(f41,plain,(
% 0.82/1.04    ~v2_struct_0(sK2)),
% 0.82/1.04    inference(cnf_transformation,[],[f27])).
% 0.82/1.04  
% 0.82/1.04  fof(f42,plain,(
% 0.82/1.04    l1_struct_0(sK2)),
% 0.82/1.04    inference(cnf_transformation,[],[f27])).
% 0.82/1.04  
% 0.82/1.04  fof(f4,axiom,(
% 0.82/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.82/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.82/1.04  
% 0.82/1.04  fof(f10,plain,(
% 0.82/1.04    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.82/1.04    inference(ennf_transformation,[],[f4])).
% 0.82/1.04  
% 0.82/1.04  fof(f11,plain,(
% 0.82/1.04    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.82/1.04    inference(flattening,[],[f10])).
% 0.82/1.04  
% 0.82/1.04  fof(f23,plain,(
% 0.82/1.04    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.82/1.04    inference(nnf_transformation,[],[f11])).
% 0.82/1.04  
% 0.82/1.04  fof(f39,plain,(
% 0.82/1.04    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.82/1.04    inference(cnf_transformation,[],[f23])).
% 0.82/1.04  
% 0.82/1.04  fof(f48,plain,(
% 0.82/1.04    ~r2_waybel_0(sK2,sK3,sK4)),
% 0.82/1.04    inference(cnf_transformation,[],[f27])).
% 0.82/1.04  
% 0.82/1.04  fof(f47,plain,(
% 0.82/1.04    r1_waybel_0(sK2,sK3,sK4)),
% 0.82/1.04    inference(cnf_transformation,[],[f27])).
% 0.82/1.04  
% 0.82/1.04  cnf(c_4,plain,
% 0.82/1.04      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
% 0.82/1.04      inference(cnf_transformation,[],[f56]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_1104,plain,
% 0.82/1.04      ( ~ r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),k6_subset_1(X0,sK4))
% 0.82/1.04      | ~ r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),sK4) ),
% 0.82/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_1244,plain,
% 0.82/1.04      ( ~ r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),k6_subset_1(u1_struct_0(sK2),sK4))
% 0.82/1.04      | ~ r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),sK4) ),
% 0.82/1.04      inference(instantiation,[status(thm)],[c_1104]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_8,plain,
% 0.82/1.04      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 0.82/1.04      inference(cnf_transformation,[],[f34]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_943,plain,
% 0.82/1.04      ( r1_xboole_0(k6_subset_1(u1_struct_0(sK2),sK4),sK4)
% 0.82/1.04      | r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),k6_subset_1(u1_struct_0(sK2),sK4)) ),
% 0.82/1.04      inference(instantiation,[status(thm)],[c_8]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_7,plain,
% 0.82/1.04      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 0.82/1.04      inference(cnf_transformation,[],[f35]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_944,plain,
% 0.82/1.04      ( r1_xboole_0(k6_subset_1(u1_struct_0(sK2),sK4),sK4)
% 0.82/1.04      | r2_hidden(sK1(k6_subset_1(u1_struct_0(sK2),sK4),sK4),sK4) ),
% 0.82/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_14,negated_conjecture,
% 0.82/1.04      ( l1_waybel_0(sK3,sK2) ),
% 0.82/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_11,plain,
% 0.82/1.04      ( ~ r1_waybel_0(X0,X1,X2)
% 0.82/1.04      | ~ r1_waybel_0(X0,X1,X3)
% 0.82/1.04      | ~ l1_waybel_0(X1,X0)
% 0.82/1.04      | ~ r1_xboole_0(X3,X2)
% 0.82/1.04      | ~ v4_orders_2(X1)
% 0.82/1.04      | ~ v7_waybel_0(X1)
% 0.82/1.04      | ~ l1_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X1) ),
% 0.82/1.04      inference(cnf_transformation,[],[f40]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_15,negated_conjecture,
% 0.82/1.04      ( v7_waybel_0(sK3) ),
% 0.82/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_212,plain,
% 0.82/1.04      ( ~ r1_waybel_0(X0,X1,X2)
% 0.82/1.04      | ~ r1_waybel_0(X0,X1,X3)
% 0.82/1.04      | ~ l1_waybel_0(X1,X0)
% 0.82/1.04      | ~ r1_xboole_0(X3,X2)
% 0.82/1.04      | ~ v4_orders_2(X1)
% 0.82/1.04      | ~ l1_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X1)
% 0.82/1.04      | sK3 != X1 ),
% 0.82/1.04      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_213,plain,
% 0.82/1.04      ( ~ r1_waybel_0(X0,sK3,X1)
% 0.82/1.04      | ~ r1_waybel_0(X0,sK3,X2)
% 0.82/1.04      | ~ l1_waybel_0(sK3,X0)
% 0.82/1.04      | ~ r1_xboole_0(X1,X2)
% 0.82/1.04      | ~ v4_orders_2(sK3)
% 0.82/1.04      | ~ l1_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X0)
% 0.82/1.04      | v2_struct_0(sK3) ),
% 0.82/1.04      inference(unflattening,[status(thm)],[c_212]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_17,negated_conjecture,
% 0.82/1.04      ( ~ v2_struct_0(sK3) ),
% 0.82/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_16,negated_conjecture,
% 0.82/1.04      ( v4_orders_2(sK3) ),
% 0.82/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_217,plain,
% 0.82/1.04      ( v2_struct_0(X0)
% 0.82/1.04      | ~ l1_struct_0(X0)
% 0.82/1.04      | ~ r1_waybel_0(X0,sK3,X1)
% 0.82/1.04      | ~ r1_waybel_0(X0,sK3,X2)
% 0.82/1.04      | ~ l1_waybel_0(sK3,X0)
% 0.82/1.04      | ~ r1_xboole_0(X1,X2) ),
% 0.82/1.04      inference(global_propositional_subsumption,
% 0.82/1.04                [status(thm)],
% 0.82/1.04                [c_213,c_17,c_16]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_218,plain,
% 0.82/1.04      ( ~ r1_waybel_0(X0,sK3,X1)
% 0.82/1.04      | ~ r1_waybel_0(X0,sK3,X2)
% 0.82/1.04      | ~ l1_waybel_0(sK3,X0)
% 0.82/1.04      | ~ r1_xboole_0(X2,X1)
% 0.82/1.04      | ~ l1_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X0) ),
% 0.82/1.04      inference(renaming,[status(thm)],[c_217]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_263,plain,
% 0.82/1.04      ( ~ r1_waybel_0(X0,sK3,X1)
% 0.82/1.04      | ~ r1_waybel_0(X0,sK3,X2)
% 0.82/1.04      | ~ r1_xboole_0(X1,X2)
% 0.82/1.04      | ~ l1_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X0)
% 0.82/1.04      | sK3 != sK3
% 0.82/1.04      | sK2 != X0 ),
% 0.82/1.04      inference(resolution_lifted,[status(thm)],[c_14,c_218]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_264,plain,
% 0.82/1.04      ( ~ r1_waybel_0(sK2,sK3,X0)
% 0.82/1.04      | ~ r1_waybel_0(sK2,sK3,X1)
% 0.82/1.04      | ~ r1_xboole_0(X1,X0)
% 0.82/1.04      | ~ l1_struct_0(sK2)
% 0.82/1.04      | v2_struct_0(sK2) ),
% 0.82/1.04      inference(unflattening,[status(thm)],[c_263]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_19,negated_conjecture,
% 0.82/1.04      ( ~ v2_struct_0(sK2) ),
% 0.82/1.04      inference(cnf_transformation,[],[f41]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_18,negated_conjecture,
% 0.82/1.04      ( l1_struct_0(sK2) ),
% 0.82/1.04      inference(cnf_transformation,[],[f42]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_268,plain,
% 0.82/1.04      ( ~ r1_waybel_0(sK2,sK3,X0)
% 0.82/1.04      | ~ r1_waybel_0(sK2,sK3,X1)
% 0.82/1.04      | ~ r1_xboole_0(X1,X0) ),
% 0.82/1.04      inference(global_propositional_subsumption,
% 0.82/1.04                [status(thm)],
% 0.82/1.04                [c_264,c_19,c_18]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_269,plain,
% 0.82/1.04      ( ~ r1_waybel_0(sK2,sK3,X0)
% 0.82/1.04      | ~ r1_waybel_0(sK2,sK3,X1)
% 0.82/1.04      | ~ r1_xboole_0(X0,X1) ),
% 0.82/1.04      inference(renaming,[status(thm)],[c_268]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_811,plain,
% 0.82/1.04      ( ~ r1_waybel_0(sK2,sK3,X0)
% 0.82/1.04      | ~ r1_waybel_0(sK2,sK3,k6_subset_1(u1_struct_0(sK2),sK4))
% 0.82/1.04      | ~ r1_xboole_0(k6_subset_1(u1_struct_0(sK2),sK4),X0) ),
% 0.82/1.04      inference(instantiation,[status(thm)],[c_269]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_893,plain,
% 0.82/1.04      ( ~ r1_waybel_0(sK2,sK3,k6_subset_1(u1_struct_0(sK2),sK4))
% 0.82/1.04      | ~ r1_waybel_0(sK2,sK3,sK4)
% 0.82/1.04      | ~ r1_xboole_0(k6_subset_1(u1_struct_0(sK2),sK4),sK4) ),
% 0.82/1.04      inference(instantiation,[status(thm)],[c_811]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_9,plain,
% 0.82/1.04      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 0.82/1.04      | r2_waybel_0(X0,X1,X2)
% 0.82/1.04      | ~ l1_waybel_0(X1,X0)
% 0.82/1.04      | ~ l1_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X1) ),
% 0.82/1.04      inference(cnf_transformation,[],[f39]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_12,negated_conjecture,
% 0.82/1.04      ( ~ r2_waybel_0(sK2,sK3,sK4) ),
% 0.82/1.04      inference(cnf_transformation,[],[f48]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_250,plain,
% 0.82/1.04      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 0.82/1.04      | ~ l1_waybel_0(X1,X0)
% 0.82/1.04      | ~ l1_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X0)
% 0.82/1.04      | v2_struct_0(X1)
% 0.82/1.04      | sK4 != X2
% 0.82/1.04      | sK3 != X1
% 0.82/1.04      | sK2 != X0 ),
% 0.82/1.04      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_251,plain,
% 0.82/1.04      ( r1_waybel_0(sK2,sK3,k6_subset_1(u1_struct_0(sK2),sK4))
% 0.82/1.04      | ~ l1_waybel_0(sK3,sK2)
% 0.82/1.04      | ~ l1_struct_0(sK2)
% 0.82/1.04      | v2_struct_0(sK3)
% 0.82/1.04      | v2_struct_0(sK2) ),
% 0.82/1.04      inference(unflattening,[status(thm)],[c_250]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(c_13,negated_conjecture,
% 0.82/1.04      ( r1_waybel_0(sK2,sK3,sK4) ),
% 0.82/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.82/1.04  
% 0.82/1.04  cnf(contradiction,plain,
% 0.82/1.04      ( $false ),
% 0.82/1.04      inference(minisat,
% 0.82/1.04                [status(thm)],
% 0.82/1.04                [c_1244,c_943,c_944,c_893,c_251,c_13,c_14,c_17,c_18,c_19]) ).
% 0.82/1.04  
% 0.82/1.04  
% 0.82/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.82/1.04  
% 0.82/1.04  ------                               Statistics
% 0.82/1.04  
% 0.82/1.04  ------ General
% 0.82/1.04  
% 0.82/1.04  abstr_ref_over_cycles:                  0
% 0.82/1.04  abstr_ref_under_cycles:                 0
% 0.82/1.04  gc_basic_clause_elim:                   0
% 0.82/1.04  forced_gc_time:                         0
% 0.82/1.04  parsing_time:                           0.009
% 0.82/1.04  unif_index_cands_time:                  0.
% 0.82/1.04  unif_index_add_time:                    0.
% 0.82/1.04  orderings_time:                         0.
% 0.82/1.04  out_proof_time:                         0.007
% 0.82/1.04  total_time:                             0.122
% 0.82/1.04  num_of_symbols:                         47
% 0.82/1.04  num_of_terms:                           926
% 0.82/1.04  
% 0.82/1.04  ------ Preprocessing
% 0.82/1.04  
% 0.82/1.04  num_of_splits:                          0
% 0.82/1.04  num_of_split_atoms:                     0
% 0.82/1.04  num_of_reused_defs:                     0
% 0.82/1.04  num_eq_ax_congr_red:                    23
% 0.82/1.04  num_of_sem_filtered_clauses:            1
% 0.82/1.04  num_of_subtypes:                        0
% 0.82/1.04  monotx_restored_types:                  0
% 0.82/1.04  sat_num_of_epr_types:                   0
% 0.82/1.04  sat_num_of_non_cyclic_types:            0
% 0.82/1.04  sat_guarded_non_collapsed_types:        0
% 0.82/1.04  num_pure_diseq_elim:                    0
% 0.82/1.04  simp_replaced_by:                       0
% 0.82/1.04  res_preprocessed:                       69
% 0.82/1.04  prep_upred:                             0
% 0.82/1.04  prep_unflattend:                        5
% 0.82/1.04  smt_new_axioms:                         0
% 0.82/1.04  pred_elim_cands:                        3
% 0.82/1.04  pred_elim:                              6
% 0.82/1.04  pred_elim_cl:                           8
% 0.82/1.04  pred_elim_cycles:                       8
% 0.82/1.04  merged_defs:                            0
% 0.82/1.04  merged_defs_ncl:                        0
% 0.82/1.04  bin_hyper_res:                          0
% 0.82/1.04  prep_cycles:                            4
% 0.82/1.04  pred_elim_time:                         0.018
% 0.82/1.04  splitting_time:                         0.
% 0.82/1.04  sem_filter_time:                        0.
% 0.82/1.04  monotx_time:                            0.001
% 0.82/1.04  subtype_inf_time:                       0.
% 0.82/1.04  
% 0.82/1.04  ------ Problem properties
% 0.82/1.04  
% 0.82/1.04  clauses:                                12
% 0.82/1.04  conjectures:                            1
% 0.82/1.04  epr:                                    3
% 0.82/1.04  horn:                                   6
% 0.82/1.04  ground:                                 2
% 0.82/1.04  unary:                                  2
% 0.82/1.04  binary:                                 4
% 0.82/1.04  lits:                                   29
% 0.82/1.04  lits_eq:                                3
% 0.82/1.04  fd_pure:                                0
% 0.82/1.04  fd_pseudo:                              0
% 0.82/1.04  fd_cond:                                0
% 0.82/1.04  fd_pseudo_cond:                         3
% 0.82/1.04  ac_symbols:                             0
% 0.82/1.04  
% 0.82/1.04  ------ Propositional Solver
% 0.82/1.04  
% 0.82/1.04  prop_solver_calls:                      25
% 0.82/1.04  prop_fast_solver_calls:                 423
% 0.82/1.04  smt_solver_calls:                       0
% 0.82/1.04  smt_fast_solver_calls:                  0
% 0.82/1.04  prop_num_of_clauses:                    361
% 0.82/1.04  prop_preprocess_simplified:             2241
% 0.82/1.04  prop_fo_subsumed:                       8
% 0.82/1.04  prop_solver_time:                       0.
% 0.82/1.04  smt_solver_time:                        0.
% 0.82/1.04  smt_fast_solver_time:                   0.
% 0.82/1.04  prop_fast_solver_time:                  0.
% 0.82/1.04  prop_unsat_core_time:                   0.
% 0.82/1.04  
% 0.82/1.04  ------ QBF
% 0.82/1.04  
% 0.82/1.04  qbf_q_res:                              0
% 0.82/1.04  qbf_num_tautologies:                    0
% 0.82/1.04  qbf_prep_cycles:                        0
% 0.82/1.04  
% 0.82/1.04  ------ BMC1
% 0.82/1.04  
% 0.82/1.04  bmc1_current_bound:                     -1
% 0.82/1.04  bmc1_last_solved_bound:                 -1
% 0.82/1.04  bmc1_unsat_core_size:                   -1
% 0.82/1.04  bmc1_unsat_core_parents_size:           -1
% 0.82/1.04  bmc1_merge_next_fun:                    0
% 0.82/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.82/1.04  
% 0.82/1.04  ------ Instantiation
% 0.82/1.04  
% 0.82/1.04  inst_num_of_clauses:                    92
% 0.82/1.04  inst_num_in_passive:                    33
% 0.82/1.04  inst_num_in_active:                     49
% 0.82/1.04  inst_num_in_unprocessed:                9
% 0.82/1.04  inst_num_of_loops:                      52
% 0.82/1.04  inst_num_of_learning_restarts:          0
% 0.82/1.04  inst_num_moves_active_passive:          0
% 0.82/1.04  inst_lit_activity:                      0
% 0.82/1.04  inst_lit_activity_moves:                0
% 0.82/1.04  inst_num_tautologies:                   0
% 0.82/1.04  inst_num_prop_implied:                  0
% 0.82/1.04  inst_num_existing_simplified:           0
% 0.82/1.04  inst_num_eq_res_simplified:             0
% 0.82/1.04  inst_num_child_elim:                    0
% 0.82/1.04  inst_num_of_dismatching_blockings:      1
% 0.82/1.04  inst_num_of_non_proper_insts:           46
% 0.82/1.04  inst_num_of_duplicates:                 0
% 0.82/1.04  inst_inst_num_from_inst_to_res:         0
% 0.82/1.04  inst_dismatching_checking_time:         0.
% 0.82/1.04  
% 0.82/1.04  ------ Resolution
% 0.82/1.04  
% 0.82/1.04  res_num_of_clauses:                     0
% 0.82/1.04  res_num_in_passive:                     0
% 0.82/1.04  res_num_in_active:                      0
% 0.82/1.04  res_num_of_loops:                       73
% 0.82/1.04  res_forward_subset_subsumed:            0
% 0.82/1.04  res_backward_subset_subsumed:           0
% 0.82/1.04  res_forward_subsumed:                   0
% 0.82/1.04  res_backward_subsumed:                  0
% 0.82/1.04  res_forward_subsumption_resolution:     0
% 0.82/1.04  res_backward_subsumption_resolution:    0
% 0.82/1.04  res_clause_to_clause_subsumption:       42
% 0.82/1.04  res_orphan_elimination:                 0
% 0.82/1.04  res_tautology_del:                      5
% 0.82/1.04  res_num_eq_res_simplified:              0
% 0.82/1.04  res_num_sel_changes:                    0
% 0.82/1.04  res_moves_from_active_to_pass:          0
% 0.82/1.04  
% 0.82/1.04  ------ Superposition
% 0.82/1.04  
% 0.82/1.04  sup_time_total:                         0.
% 0.82/1.04  sup_time_generating:                    0.
% 0.82/1.04  sup_time_sim_full:                      0.
% 0.82/1.04  sup_time_sim_immed:                     0.
% 0.82/1.04  
% 0.82/1.04  sup_num_of_clauses:                     18
% 0.82/1.04  sup_num_in_active:                      10
% 0.82/1.04  sup_num_in_passive:                     8
% 0.82/1.04  sup_num_of_loops:                       10
% 0.82/1.04  sup_fw_superposition:                   4
% 0.82/1.04  sup_bw_superposition:                   2
% 0.82/1.04  sup_immediate_simplified:               0
% 0.82/1.04  sup_given_eliminated:                   0
% 0.82/1.04  comparisons_done:                       0
% 0.82/1.04  comparisons_avoided:                    0
% 0.82/1.04  
% 0.82/1.04  ------ Simplifications
% 0.82/1.04  
% 0.82/1.04  
% 0.82/1.04  sim_fw_subset_subsumed:                 0
% 0.82/1.04  sim_bw_subset_subsumed:                 0
% 0.82/1.04  sim_fw_subsumed:                        0
% 0.82/1.04  sim_bw_subsumed:                        0
% 0.82/1.04  sim_fw_subsumption_res:                 0
% 0.82/1.04  sim_bw_subsumption_res:                 0
% 0.82/1.04  sim_tautology_del:                      0
% 0.82/1.04  sim_eq_tautology_del:                   0
% 0.82/1.04  sim_eq_res_simp:                        0
% 0.82/1.04  sim_fw_demodulated:                     0
% 0.82/1.04  sim_bw_demodulated:                     0
% 0.82/1.04  sim_light_normalised:                   0
% 0.82/1.04  sim_joinable_taut:                      0
% 0.82/1.04  sim_joinable_simp:                      0
% 0.82/1.04  sim_ac_normalised:                      0
% 0.82/1.04  sim_smt_subsumption:                    0
% 0.82/1.04  
%------------------------------------------------------------------------------
