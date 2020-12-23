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
% DateTime   : Thu Dec  3 12:28:09 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 277 expanded)
%              Number of clauses        :   50 (  82 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   20
%              Number of atoms          :  477 (1371 expanded)
%              Number of equality atoms :   67 ( 199 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK6,u1_struct_0(X0))
        & l1_waybel_0(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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

fof(f43,plain,
    ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5))
    & l1_waybel_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f42,f41])).

fof(f65,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f33])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5))
        & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f38,f37])).

fof(f58,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_695,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_699,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2077,plain,
    ( k6_subset_1(X0,X1) = X0
    | r2_hidden(sK1(X0,X1,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_699])).

cnf(c_2079,plain,
    ( k6_subset_1(X0,X1) = X0
    | r2_hidden(sK1(X0,X1,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2077])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_704,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2363,plain,
    ( k6_subset_1(X0,X1) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2079,c_704])).

cnf(c_2559,plain,
    ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_695,c_2363])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_697,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2570,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2559,c_697])).

cnf(c_2669,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_2570])).

cnf(c_2684,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2669,c_2570])).

cnf(c_2825,plain,
    ( k6_subset_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_2684])).

cnf(c_2834,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2825,c_2559])).

cnf(c_3466,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2834,c_704])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,plain,
    ( l1_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,plain,
    ( l1_waybel_0(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1018,plain,
    ( m1_subset_1(sK2(u1_struct_0(X0)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1311,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_1312,plain,
    ( m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_13,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1164,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(sK2(u1_struct_0(X1)),u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,sK2(u1_struct_0(X1)))),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1444,plain,
    ( ~ r2_waybel_0(sK5,sK6,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6))
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1164])).

cnf(c_1445,plain,
    ( r2_waybel_0(sK5,sK6,X0) != iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_20,negated_conjecture,
    ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2143,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X2)
    | r2_hidden(sK0(k6_subset_1(X0,X1),X2),X0) ),
    inference(resolution,[status(thm)],[c_8,c_2])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2865,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[status(thm)],[c_2143,c_1])).

cnf(c_19,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_tarski(X2,X3)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_16,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2611,plain,
    ( r1_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_tarski(k6_subset_1(u1_struct_0(X0),X3),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_19,c_16])).

cnf(c_2875,plain,
    ( r1_waybel_0(X0,X1,u1_struct_0(X0))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2865,c_2611])).

cnf(c_3073,plain,
    ( r2_waybel_0(sK5,sK6,X0)
    | ~ l1_waybel_0(sK6,sK5)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5) ),
    inference(resolution,[status(thm)],[c_20,c_2875])).

cnf(c_3074,plain,
    ( r2_waybel_0(sK5,sK6,X0) = iProver_top
    | l1_waybel_0(sK6,sK5) != iProver_top
    | l1_struct_0(sK5) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3073])).

cnf(c_3305,plain,
    ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3306,plain,
    ( r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3305])).

cnf(c_3501,plain,
    ( v1_xboole_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3466,c_25,c_26,c_27,c_28,c_1312,c_1445,c_3074,c_3306])).

cnf(c_3508,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_695,c_3501])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:44:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.29/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.99  
% 3.29/0.99  ------  iProver source info
% 3.29/0.99  
% 3.29/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.99  git: non_committed_changes: false
% 3.29/0.99  git: last_make_outside_of_git: false
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  ------ Parsing...
% 3.29/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.99  ------ Proving...
% 3.29/0.99  ------ Problem Properties 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  clauses                                 25
% 3.29/0.99  conjectures                             5
% 3.29/0.99  EPR                                     8
% 3.29/0.99  Horn                                    11
% 3.29/0.99  unary                                   7
% 3.29/0.99  binary                                  5
% 3.29/0.99  lits                                    91
% 3.29/0.99  lits eq                                 3
% 3.29/0.99  fd_pure                                 0
% 3.29/0.99  fd_pseudo                               0
% 3.29/0.99  fd_cond                                 0
% 3.29/0.99  fd_pseudo_cond                          3
% 3.29/0.99  AC symbols                              0
% 3.29/0.99  
% 3.29/0.99  ------ Input Options Time Limit: Unbounded
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  Current options:
% 3.29/0.99  ------ 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ Proving...
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS status Theorem for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99   Resolution empty clause
% 3.29/0.99  
% 3.29/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  fof(f4,axiom,(
% 3.29/0.99    v1_xboole_0(k1_xboole_0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f53,plain,(
% 3.29/0.99    v1_xboole_0(k1_xboole_0)),
% 3.29/0.99    inference(cnf_transformation,[],[f4])).
% 3.29/0.99  
% 3.29/0.99  fof(f3,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f28,plain,(
% 3.29/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.99    inference(nnf_transformation,[],[f3])).
% 3.29/0.99  
% 3.29/0.99  fof(f29,plain,(
% 3.29/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.99    inference(flattening,[],[f28])).
% 3.29/0.99  
% 3.29/0.99  fof(f30,plain,(
% 3.29/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.99    inference(rectify,[],[f29])).
% 3.29/0.99  
% 3.29/0.99  fof(f31,plain,(
% 3.29/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f32,plain,(
% 3.29/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.29/0.99  
% 3.29/0.99  fof(f50,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f32])).
% 3.29/0.99  
% 3.29/0.99  fof(f6,axiom,(
% 3.29/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f55,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f6])).
% 3.29/0.99  
% 3.29/0.99  fof(f72,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.29/0.99    inference(definition_unfolding,[],[f50,f55])).
% 3.29/0.99  
% 3.29/0.99  fof(f1,axiom,(
% 3.29/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f13,plain,(
% 3.29/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.29/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 3.29/0.99  
% 3.29/0.99  fof(f16,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.29/0.99    inference(ennf_transformation,[],[f13])).
% 3.29/0.99  
% 3.29/0.99  fof(f44,plain,(
% 3.29/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f16])).
% 3.29/0.99  
% 3.29/0.99  fof(f48,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.29/0.99    inference(cnf_transformation,[],[f32])).
% 3.29/0.99  
% 3.29/0.99  fof(f74,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 3.29/0.99    inference(definition_unfolding,[],[f48,f55])).
% 3.29/0.99  
% 3.29/0.99  fof(f77,plain,(
% 3.29/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 3.29/0.99    inference(equality_resolution,[],[f74])).
% 3.29/0.99  
% 3.29/0.99  fof(f10,conjecture,(
% 3.29/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f11,negated_conjecture,(
% 3.29/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.29/0.99    inference(negated_conjecture,[],[f10])).
% 3.29/0.99  
% 3.29/0.99  fof(f14,plain,(
% 3.29/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.29/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.29/0.99  
% 3.29/0.99  fof(f15,plain,(
% 3.29/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.29/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.29/0.99  
% 3.29/0.99  fof(f24,plain,(
% 3.29/0.99    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.29/0.99    inference(ennf_transformation,[],[f15])).
% 3.29/0.99  
% 3.29/0.99  fof(f25,plain,(
% 3.29/0.99    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.29/0.99    inference(flattening,[],[f24])).
% 3.29/0.99  
% 3.29/0.99  fof(f42,plain,(
% 3.29/0.99    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK6,u1_struct_0(X0)) & l1_waybel_0(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f41,plain,(
% 3.29/0.99    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK5,X1,u1_struct_0(sK5)) & l1_waybel_0(X1,sK5) & ~v2_struct_0(X1)) & l1_struct_0(sK5) & ~v2_struct_0(sK5))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f43,plain,(
% 3.29/0.99    (~r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) & l1_waybel_0(sK6,sK5) & ~v2_struct_0(sK6)) & l1_struct_0(sK5) & ~v2_struct_0(sK5)),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f42,f41])).
% 3.29/0.99  
% 3.29/0.99  fof(f65,plain,(
% 3.29/0.99    ~v2_struct_0(sK5)),
% 3.29/0.99    inference(cnf_transformation,[],[f43])).
% 3.29/0.99  
% 3.29/0.99  fof(f66,plain,(
% 3.29/0.99    l1_struct_0(sK5)),
% 3.29/0.99    inference(cnf_transformation,[],[f43])).
% 3.29/0.99  
% 3.29/0.99  fof(f67,plain,(
% 3.29/0.99    ~v2_struct_0(sK6)),
% 3.29/0.99    inference(cnf_transformation,[],[f43])).
% 3.29/0.99  
% 3.29/0.99  fof(f68,plain,(
% 3.29/0.99    l1_waybel_0(sK6,sK5)),
% 3.29/0.99    inference(cnf_transformation,[],[f43])).
% 3.29/0.99  
% 3.29/0.99  fof(f5,axiom,(
% 3.29/0.99    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f33,plain,(
% 3.29/0.99    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f34,plain,(
% 3.29/0.99    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f33])).
% 3.29/0.99  
% 3.29/0.99  fof(f54,plain,(
% 3.29/0.99    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f34])).
% 3.29/0.99  
% 3.29/0.99  fof(f7,axiom,(
% 3.29/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f18,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.29/0.99    inference(ennf_transformation,[],[f7])).
% 3.29/0.99  
% 3.29/0.99  fof(f19,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.29/0.99    inference(flattening,[],[f18])).
% 3.29/0.99  
% 3.29/0.99  fof(f35,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.29/0.99    inference(nnf_transformation,[],[f19])).
% 3.29/0.99  
% 3.29/0.99  fof(f36,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.29/0.99    inference(rectify,[],[f35])).
% 3.29/0.99  
% 3.29/0.99  fof(f38,plain,(
% 3.29/0.99    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5)) & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1))))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f37,plain,(
% 3.29/0.99    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f39,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK4(X0,X1,X2,X5)) & m1_subset_1(sK4(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f38,f37])).
% 3.29/0.99  
% 3.29/0.99  fof(f58,plain,(
% 3.29/0.99    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f39])).
% 3.29/0.99  
% 3.29/0.99  fof(f69,plain,(
% 3.29/0.99    ~r1_waybel_0(sK5,sK6,u1_struct_0(sK5))),
% 3.29/0.99    inference(cnf_transformation,[],[f43])).
% 3.29/0.99  
% 3.29/0.99  fof(f47,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.29/0.99    inference(cnf_transformation,[],[f32])).
% 3.29/0.99  
% 3.29/0.99  fof(f75,plain,(
% 3.29/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 3.29/0.99    inference(definition_unfolding,[],[f47,f55])).
% 3.29/0.99  
% 3.29/0.99  fof(f78,plain,(
% 3.29/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 3.29/0.99    inference(equality_resolution,[],[f75])).
% 3.29/0.99  
% 3.29/0.99  fof(f2,axiom,(
% 3.29/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f12,plain,(
% 3.29/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.29/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.29/0.99  
% 3.29/0.99  fof(f17,plain,(
% 3.29/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.29/0.99    inference(ennf_transformation,[],[f12])).
% 3.29/0.99  
% 3.29/0.99  fof(f26,plain,(
% 3.29/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f27,plain,(
% 3.29/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f26])).
% 3.29/0.99  
% 3.29/0.99  fof(f45,plain,(
% 3.29/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f27])).
% 3.29/0.99  
% 3.29/0.99  fof(f46,plain,(
% 3.29/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f27])).
% 3.29/0.99  
% 3.29/0.99  fof(f9,axiom,(
% 3.29/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f22,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.29/0.99    inference(ennf_transformation,[],[f9])).
% 3.29/0.99  
% 3.29/0.99  fof(f23,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.29/0.99    inference(flattening,[],[f22])).
% 3.29/0.99  
% 3.29/0.99  fof(f63,plain,(
% 3.29/0.99    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2) | ~r1_tarski(X2,X3) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f23])).
% 3.29/0.99  
% 3.29/0.99  fof(f8,axiom,(
% 3.29/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f20,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.29/0.99    inference(ennf_transformation,[],[f8])).
% 3.29/0.99  
% 3.29/0.99  fof(f21,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.29/0.99    inference(flattening,[],[f20])).
% 3.29/0.99  
% 3.29/0.99  fof(f40,plain,(
% 3.29/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.29/0.99    inference(nnf_transformation,[],[f21])).
% 3.29/0.99  
% 3.29/0.99  fof(f62,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f40])).
% 3.29/0.99  
% 3.29/0.99  cnf(c_9,plain,
% 3.29/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_695,plain,
% 3.29/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5,plain,
% 3.29/0.99      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.29/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.29/0.99      | k6_subset_1(X0,X1) = X2 ),
% 3.29/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_699,plain,
% 3.29/0.99      ( k6_subset_1(X0,X1) = X2
% 3.29/0.99      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 3.29/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2077,plain,
% 3.29/0.99      ( k6_subset_1(X0,X1) = X0
% 3.29/0.99      | r2_hidden(sK1(X0,X1,X0),X0) = iProver_top
% 3.29/0.99      | iProver_top != iProver_top ),
% 3.29/0.99      inference(equality_factoring,[status(thm)],[c_699]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2079,plain,
% 3.29/0.99      ( k6_subset_1(X0,X1) = X0 | r2_hidden(sK1(X0,X1,X0),X0) = iProver_top ),
% 3.29/0.99      inference(equality_resolution_simp,[status(thm)],[c_2077]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_0,plain,
% 3.29/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_704,plain,
% 3.29/0.99      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2363,plain,
% 3.29/0.99      ( k6_subset_1(X0,X1) = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_2079,c_704]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2559,plain,
% 3.29/0.99      ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_695,c_2363]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_7,plain,
% 3.29/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_697,plain,
% 3.29/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.29/0.99      | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2570,plain,
% 3.29/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.29/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_2559,c_697]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2669,plain,
% 3.29/0.99      ( k6_subset_1(X0,X1) = X2
% 3.29/0.99      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 3.29/0.99      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_699,c_2570]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2684,plain,
% 3.29/0.99      ( k6_subset_1(X0,X1) = X2
% 3.29/0.99      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 3.29/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2669,c_2570]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2825,plain,
% 3.29/0.99      ( k6_subset_1(k1_xboole_0,X0) = X1
% 3.29/0.99      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_699,c_2684]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2834,plain,
% 3.29/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.29/0.99      inference(demodulation,[status(thm)],[c_2825,c_2559]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3466,plain,
% 3.29/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_2834,c_704]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_24,negated_conjecture,
% 3.29/0.99      ( ~ v2_struct_0(sK5) ),
% 3.29/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_25,plain,
% 3.29/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_23,negated_conjecture,
% 3.29/0.99      ( l1_struct_0(sK5) ),
% 3.29/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_26,plain,
% 3.29/0.99      ( l1_struct_0(sK5) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_22,negated_conjecture,
% 3.29/0.99      ( ~ v2_struct_0(sK6) ),
% 3.29/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_27,plain,
% 3.29/0.99      ( v2_struct_0(sK6) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_21,negated_conjecture,
% 3.29/0.99      ( l1_waybel_0(sK6,sK5) ),
% 3.29/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_28,plain,
% 3.29/0.99      ( l1_waybel_0(sK6,sK5) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_10,plain,
% 3.29/0.99      ( m1_subset_1(sK2(X0),X0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1018,plain,
% 3.29/0.99      ( m1_subset_1(sK2(u1_struct_0(X0)),u1_struct_0(X0)) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1311,plain,
% 3.29/0.99      ( m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1018]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1312,plain,
% 3.29/0.99      ( m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_13,plain,
% 3.29/0.99      ( ~ r2_waybel_0(X0,X1,X2)
% 3.29/0.99      | ~ l1_waybel_0(X1,X0)
% 3.29/0.99      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.29/0.99      | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
% 3.29/0.99      | ~ l1_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1164,plain,
% 3.29/0.99      ( ~ r2_waybel_0(X0,X1,X2)
% 3.29/0.99      | ~ l1_waybel_0(X1,X0)
% 3.29/0.99      | ~ m1_subset_1(sK2(u1_struct_0(X1)),u1_struct_0(X1))
% 3.29/0.99      | r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,sK2(u1_struct_0(X1)))),X2)
% 3.29/0.99      | ~ l1_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X1)
% 3.29/0.99      | v2_struct_0(X0) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1444,plain,
% 3.29/0.99      ( ~ r2_waybel_0(sK5,sK6,X0)
% 3.29/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.29/0.99      | ~ m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6))
% 3.29/0.99      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0)
% 3.29/0.99      | ~ l1_struct_0(sK5)
% 3.29/0.99      | v2_struct_0(sK6)
% 3.29/0.99      | v2_struct_0(sK5) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1164]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1445,plain,
% 3.29/0.99      ( r2_waybel_0(sK5,sK6,X0) != iProver_top
% 3.29/0.99      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.29/0.99      | m1_subset_1(sK2(u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 3.29/0.99      | r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0) = iProver_top
% 3.29/0.99      | l1_struct_0(sK5) != iProver_top
% 3.29/0.99      | v2_struct_0(sK6) = iProver_top
% 3.29/0.99      | v2_struct_0(sK5) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_20,negated_conjecture,
% 3.29/0.99      ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_8,plain,
% 3.29/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2,plain,
% 3.29/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2143,plain,
% 3.29/0.99      ( r1_tarski(k6_subset_1(X0,X1),X2)
% 3.29/0.99      | r2_hidden(sK0(k6_subset_1(X0,X1),X2),X0) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_8,c_2]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1,plain,
% 3.29/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2865,plain,
% 3.29/0.99      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_2143,c_1]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_19,plain,
% 3.29/0.99      ( ~ r1_waybel_0(X0,X1,X2)
% 3.29/0.99      | r1_waybel_0(X0,X1,X3)
% 3.29/0.99      | ~ l1_waybel_0(X1,X0)
% 3.29/0.99      | ~ r1_tarski(X2,X3)
% 3.29/0.99      | ~ l1_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_16,plain,
% 3.29/0.99      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 3.29/0.99      | r2_waybel_0(X0,X1,X2)
% 3.29/0.99      | ~ l1_waybel_0(X1,X0)
% 3.29/0.99      | ~ l1_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2611,plain,
% 3.29/0.99      ( r1_waybel_0(X0,X1,X2)
% 3.29/0.99      | r2_waybel_0(X0,X1,X3)
% 3.29/0.99      | ~ l1_waybel_0(X1,X0)
% 3.29/0.99      | ~ r1_tarski(k6_subset_1(u1_struct_0(X0),X3),X2)
% 3.29/0.99      | ~ l1_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X1)
% 3.29/0.99      | v2_struct_0(X0) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_19,c_16]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2875,plain,
% 3.29/0.99      ( r1_waybel_0(X0,X1,u1_struct_0(X0))
% 3.29/0.99      | r2_waybel_0(X0,X1,X2)
% 3.29/0.99      | ~ l1_waybel_0(X1,X0)
% 3.29/0.99      | ~ l1_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X1)
% 3.29/0.99      | v2_struct_0(X0) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_2865,c_2611]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3073,plain,
% 3.29/0.99      ( r2_waybel_0(sK5,sK6,X0)
% 3.29/0.99      | ~ l1_waybel_0(sK6,sK5)
% 3.29/0.99      | ~ l1_struct_0(sK5)
% 3.29/0.99      | v2_struct_0(sK6)
% 3.29/0.99      | v2_struct_0(sK5) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_20,c_2875]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3074,plain,
% 3.29/0.99      ( r2_waybel_0(sK5,sK6,X0) = iProver_top
% 3.29/0.99      | l1_waybel_0(sK6,sK5) != iProver_top
% 3.29/0.99      | l1_struct_0(sK5) != iProver_top
% 3.29/0.99      | v2_struct_0(sK6) = iProver_top
% 3.29/0.99      | v2_struct_0(sK5) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_3073]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3305,plain,
% 3.29/0.99      ( ~ r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0)
% 3.29/0.99      | ~ v1_xboole_0(X0) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3306,plain,
% 3.29/0.99      ( r2_hidden(k2_waybel_0(sK5,sK6,sK4(sK5,sK6,X0,sK2(u1_struct_0(sK6)))),X0) != iProver_top
% 3.29/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_3305]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3501,plain,
% 3.29/0.99      ( v1_xboole_0(X0) != iProver_top ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_3466,c_25,c_26,c_27,c_28,c_1312,c_1445,c_3074,c_3306]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3508,plain,
% 3.29/0.99      ( $false ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_695,c_3501]) ).
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  ------                               Statistics
% 3.29/0.99  
% 3.29/0.99  ------ Selected
% 3.29/0.99  
% 3.29/0.99  total_time:                             0.143
% 3.29/0.99  
%------------------------------------------------------------------------------
