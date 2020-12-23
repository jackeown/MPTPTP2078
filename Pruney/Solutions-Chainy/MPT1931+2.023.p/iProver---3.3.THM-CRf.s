%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:11 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 410 expanded)
%              Number of clauses        :   64 ( 105 expanded)
%              Number of leaves         :   17 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :  536 (2325 expanded)
%              Number of equality atoms :   96 ( 366 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ~ r1_waybel_0(X0,sK7,u1_struct_0(X0))
        & l1_waybel_0(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
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
          ( ~ r1_waybel_0(sK6,X1,u1_struct_0(sK6))
          & l1_waybel_0(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r1_waybel_0(sK6,sK7,u1_struct_0(sK6))
    & l1_waybel_0(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_struct_0(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f42,f41])).

fof(f65,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ~ r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f4,f33])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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
    inference(nnf_transformation,[],[f17])).

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
     => ( r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5))
        & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
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
            | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f38,f37])).

fof(f58,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1212,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1204,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK2(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1587,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1204])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1206,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k6_subset_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1985,plain,
    ( r2_hidden(sK2(k6_subset_1(X0,X1)),X0) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1587,c_1206])).

cnf(c_2119,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1985,c_1204])).

cnf(c_2560,plain,
    ( r2_hidden(sK2(k6_subset_1(X0,X1)),X0) = iProver_top
    | r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2119,c_1206])).

cnf(c_4985,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2560,c_1204])).

cnf(c_5143,plain,
    ( r2_hidden(sK2(k6_subset_1(X0,X1)),X0) = iProver_top
    | r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4985,c_1206])).

cnf(c_11095,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5143,c_1204])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,plain,
    ( l1_waybel_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( ~ r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
    | r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1458,plain,
    ( r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X0))
    | r2_waybel_0(sK6,sK7,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1459,plain,
    ( r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X0)) = iProver_top
    | r2_waybel_0(sK6,sK7,X0) = iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_10,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1531,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1536,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1531])).

cnf(c_13,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1479,plain,
    ( ~ r2_waybel_0(sK6,sK7,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,X1)),X0)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1567,plain,
    ( ~ r2_waybel_0(sK6,sK7,X0)
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(u1_struct_0(sK7)))),X0)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_1569,plain,
    ( r2_waybel_0(sK6,sK7,X0) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(u1_struct_0(sK7)))),X0) = iProver_top
    | l1_struct_0(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_19,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ r1_tarski(X2,X3)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1471,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0)
    | r1_waybel_0(sK6,sK7,X1)
    | ~ l1_waybel_0(sK7,sK6)
    | ~ r1_tarski(X0,X1)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1678,plain,
    ( r1_waybel_0(sK6,sK7,X0)
    | ~ r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X1))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ r1_tarski(k6_subset_1(u1_struct_0(sK6),X1),X0)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_2545,plain,
    ( ~ r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X0))
    | r1_waybel_0(sK6,sK7,u1_struct_0(sK6))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_2546,plain,
    ( r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X0)) != iProver_top
    | r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) = iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) != iProver_top
    | l1_struct_0(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2545])).

cnf(c_1956,plain,
    ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),X1),k6_subset_1(u1_struct_0(sK6),X0))
    | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2922,plain,
    ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),k6_subset_1(u1_struct_0(sK6),X0))
    | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_2923,plain,
    ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),k6_subset_1(u1_struct_0(sK6),X0)) = iProver_top
    | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2922])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1957,plain,
    ( ~ r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),X1),X1)
    | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2921,plain,
    ( ~ r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),u1_struct_0(sK6))
    | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_2927,plain,
    ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
    | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2921])).

cnf(c_3951,plain,
    ( ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(u1_struct_0(sK7)))),X0)
    | r2_hidden(sK2(X0),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3952,plain,
    ( r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(u1_struct_0(sK7)))),X0) != iProver_top
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3951])).

cnf(c_7091,plain,
    ( ~ r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),k6_subset_1(u1_struct_0(sK6),X0))
    | r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7092,plain,
    ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),k6_subset_1(u1_struct_0(sK6),X0)) != iProver_top
    | r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7091])).

cnf(c_11371,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11095,c_25,c_26,c_27,c_28,c_29,c_1459,c_1536,c_1569,c_2546,c_2923,c_2927,c_3952,c_7092])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1209,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k6_subset_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1210,plain,
    ( k6_subset_1(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2282,plain,
    ( k6_subset_1(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_1210])).

cnf(c_3504,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
    | r2_hidden(sK1(X0,X0,k6_subset_1(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_1206])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1207,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3505,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
    | r2_hidden(sK1(X0,X0,k6_subset_1(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_1207])).

cnf(c_6424,plain,
    ( k6_subset_1(X0,X0) = k6_subset_1(X1,X1) ),
    inference(superposition,[status(thm)],[c_3504,c_3505])).

cnf(c_7289,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6424,c_1206])).

cnf(c_7290,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6424,c_1207])).

cnf(c_7416,plain,
    ( r2_hidden(X0,k6_subset_1(X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7289,c_7290])).

cnf(c_11382,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_11371,c_7416])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.26/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/1.00  
% 3.26/1.00  ------  iProver source info
% 3.26/1.00  
% 3.26/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.26/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/1.00  git: non_committed_changes: false
% 3.26/1.00  git: last_make_outside_of_git: false
% 3.26/1.00  
% 3.26/1.00  ------ 
% 3.26/1.00  
% 3.26/1.00  ------ Input Options
% 3.26/1.00  
% 3.26/1.00  --out_options                           all
% 3.26/1.00  --tptp_safe_out                         true
% 3.26/1.00  --problem_path                          ""
% 3.26/1.00  --include_path                          ""
% 3.26/1.00  --clausifier                            res/vclausify_rel
% 3.26/1.00  --clausifier_options                    --mode clausify
% 3.26/1.00  --stdin                                 false
% 3.26/1.00  --stats_out                             all
% 3.26/1.00  
% 3.26/1.00  ------ General Options
% 3.26/1.00  
% 3.26/1.00  --fof                                   false
% 3.26/1.00  --time_out_real                         305.
% 3.26/1.00  --time_out_virtual                      -1.
% 3.26/1.00  --symbol_type_check                     false
% 3.26/1.00  --clausify_out                          false
% 3.26/1.00  --sig_cnt_out                           false
% 3.26/1.00  --trig_cnt_out                          false
% 3.26/1.00  --trig_cnt_out_tolerance                1.
% 3.26/1.00  --trig_cnt_out_sk_spl                   false
% 3.26/1.00  --abstr_cl_out                          false
% 3.26/1.00  
% 3.26/1.00  ------ Global Options
% 3.26/1.00  
% 3.26/1.00  --schedule                              default
% 3.26/1.00  --add_important_lit                     false
% 3.26/1.00  --prop_solver_per_cl                    1000
% 3.26/1.00  --min_unsat_core                        false
% 3.26/1.00  --soft_assumptions                      false
% 3.26/1.00  --soft_lemma_size                       3
% 3.26/1.00  --prop_impl_unit_size                   0
% 3.26/1.00  --prop_impl_unit                        []
% 3.26/1.00  --share_sel_clauses                     true
% 3.26/1.00  --reset_solvers                         false
% 3.26/1.00  --bc_imp_inh                            [conj_cone]
% 3.26/1.00  --conj_cone_tolerance                   3.
% 3.26/1.00  --extra_neg_conj                        none
% 3.26/1.00  --large_theory_mode                     true
% 3.26/1.00  --prolific_symb_bound                   200
% 3.26/1.00  --lt_threshold                          2000
% 3.26/1.00  --clause_weak_htbl                      true
% 3.26/1.00  --gc_record_bc_elim                     false
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing Options
% 3.26/1.00  
% 3.26/1.00  --preprocessing_flag                    true
% 3.26/1.00  --time_out_prep_mult                    0.1
% 3.26/1.00  --splitting_mode                        input
% 3.26/1.00  --splitting_grd                         true
% 3.26/1.00  --splitting_cvd                         false
% 3.26/1.00  --splitting_cvd_svl                     false
% 3.26/1.00  --splitting_nvd                         32
% 3.26/1.00  --sub_typing                            true
% 3.26/1.00  --prep_gs_sim                           true
% 3.26/1.00  --prep_unflatten                        true
% 3.26/1.00  --prep_res_sim                          true
% 3.26/1.00  --prep_upred                            true
% 3.26/1.00  --prep_sem_filter                       exhaustive
% 3.26/1.00  --prep_sem_filter_out                   false
% 3.26/1.00  --pred_elim                             true
% 3.26/1.00  --res_sim_input                         true
% 3.26/1.00  --eq_ax_congr_red                       true
% 3.26/1.00  --pure_diseq_elim                       true
% 3.26/1.00  --brand_transform                       false
% 3.26/1.00  --non_eq_to_eq                          false
% 3.26/1.00  --prep_def_merge                        true
% 3.26/1.00  --prep_def_merge_prop_impl              false
% 3.26/1.00  --prep_def_merge_mbd                    true
% 3.26/1.00  --prep_def_merge_tr_red                 false
% 3.26/1.00  --prep_def_merge_tr_cl                  false
% 3.26/1.00  --smt_preprocessing                     true
% 3.26/1.00  --smt_ac_axioms                         fast
% 3.26/1.00  --preprocessed_out                      false
% 3.26/1.00  --preprocessed_stats                    false
% 3.26/1.00  
% 3.26/1.00  ------ Abstraction refinement Options
% 3.26/1.00  
% 3.26/1.00  --abstr_ref                             []
% 3.26/1.00  --abstr_ref_prep                        false
% 3.26/1.00  --abstr_ref_until_sat                   false
% 3.26/1.00  --abstr_ref_sig_restrict                funpre
% 3.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/1.00  --abstr_ref_under                       []
% 3.26/1.00  
% 3.26/1.00  ------ SAT Options
% 3.26/1.00  
% 3.26/1.00  --sat_mode                              false
% 3.26/1.00  --sat_fm_restart_options                ""
% 3.26/1.00  --sat_gr_def                            false
% 3.26/1.00  --sat_epr_types                         true
% 3.26/1.00  --sat_non_cyclic_types                  false
% 3.26/1.00  --sat_finite_models                     false
% 3.26/1.00  --sat_fm_lemmas                         false
% 3.26/1.00  --sat_fm_prep                           false
% 3.26/1.00  --sat_fm_uc_incr                        true
% 3.26/1.00  --sat_out_model                         small
% 3.26/1.00  --sat_out_clauses                       false
% 3.26/1.00  
% 3.26/1.00  ------ QBF Options
% 3.26/1.00  
% 3.26/1.00  --qbf_mode                              false
% 3.26/1.00  --qbf_elim_univ                         false
% 3.26/1.00  --qbf_dom_inst                          none
% 3.26/1.00  --qbf_dom_pre_inst                      false
% 3.26/1.00  --qbf_sk_in                             false
% 3.26/1.00  --qbf_pred_elim                         true
% 3.26/1.00  --qbf_split                             512
% 3.26/1.00  
% 3.26/1.00  ------ BMC1 Options
% 3.26/1.00  
% 3.26/1.00  --bmc1_incremental                      false
% 3.26/1.00  --bmc1_axioms                           reachable_all
% 3.26/1.00  --bmc1_min_bound                        0
% 3.26/1.00  --bmc1_max_bound                        -1
% 3.26/1.00  --bmc1_max_bound_default                -1
% 3.26/1.00  --bmc1_symbol_reachability              true
% 3.26/1.00  --bmc1_property_lemmas                  false
% 3.26/1.00  --bmc1_k_induction                      false
% 3.26/1.00  --bmc1_non_equiv_states                 false
% 3.26/1.00  --bmc1_deadlock                         false
% 3.26/1.00  --bmc1_ucm                              false
% 3.26/1.00  --bmc1_add_unsat_core                   none
% 3.26/1.00  --bmc1_unsat_core_children              false
% 3.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/1.00  --bmc1_out_stat                         full
% 3.26/1.00  --bmc1_ground_init                      false
% 3.26/1.00  --bmc1_pre_inst_next_state              false
% 3.26/1.00  --bmc1_pre_inst_state                   false
% 3.26/1.00  --bmc1_pre_inst_reach_state             false
% 3.26/1.00  --bmc1_out_unsat_core                   false
% 3.26/1.00  --bmc1_aig_witness_out                  false
% 3.26/1.00  --bmc1_verbose                          false
% 3.26/1.00  --bmc1_dump_clauses_tptp                false
% 3.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.26/1.00  --bmc1_dump_file                        -
% 3.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.26/1.00  --bmc1_ucm_extend_mode                  1
% 3.26/1.00  --bmc1_ucm_init_mode                    2
% 3.26/1.00  --bmc1_ucm_cone_mode                    none
% 3.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.26/1.00  --bmc1_ucm_relax_model                  4
% 3.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/1.00  --bmc1_ucm_layered_model                none
% 3.26/1.00  --bmc1_ucm_max_lemma_size               10
% 3.26/1.00  
% 3.26/1.00  ------ AIG Options
% 3.26/1.00  
% 3.26/1.00  --aig_mode                              false
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation Options
% 3.26/1.00  
% 3.26/1.00  --instantiation_flag                    true
% 3.26/1.00  --inst_sos_flag                         false
% 3.26/1.00  --inst_sos_phase                        true
% 3.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel_side                     num_symb
% 3.26/1.00  --inst_solver_per_active                1400
% 3.26/1.00  --inst_solver_calls_frac                1.
% 3.26/1.00  --inst_passive_queue_type               priority_queues
% 3.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/1.00  --inst_passive_queues_freq              [25;2]
% 3.26/1.00  --inst_dismatching                      true
% 3.26/1.00  --inst_eager_unprocessed_to_passive     true
% 3.26/1.00  --inst_prop_sim_given                   true
% 3.26/1.00  --inst_prop_sim_new                     false
% 3.26/1.00  --inst_subs_new                         false
% 3.26/1.00  --inst_eq_res_simp                      false
% 3.26/1.00  --inst_subs_given                       false
% 3.26/1.00  --inst_orphan_elimination               true
% 3.26/1.00  --inst_learning_loop_flag               true
% 3.26/1.00  --inst_learning_start                   3000
% 3.26/1.00  --inst_learning_factor                  2
% 3.26/1.00  --inst_start_prop_sim_after_learn       3
% 3.26/1.00  --inst_sel_renew                        solver
% 3.26/1.00  --inst_lit_activity_flag                true
% 3.26/1.00  --inst_restr_to_given                   false
% 3.26/1.00  --inst_activity_threshold               500
% 3.26/1.00  --inst_out_proof                        true
% 3.26/1.00  
% 3.26/1.00  ------ Resolution Options
% 3.26/1.00  
% 3.26/1.00  --resolution_flag                       true
% 3.26/1.00  --res_lit_sel                           adaptive
% 3.26/1.00  --res_lit_sel_side                      none
% 3.26/1.00  --res_ordering                          kbo
% 3.26/1.00  --res_to_prop_solver                    active
% 3.26/1.00  --res_prop_simpl_new                    false
% 3.26/1.00  --res_prop_simpl_given                  true
% 3.26/1.00  --res_passive_queue_type                priority_queues
% 3.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/1.00  --res_passive_queues_freq               [15;5]
% 3.26/1.00  --res_forward_subs                      full
% 3.26/1.00  --res_backward_subs                     full
% 3.26/1.00  --res_forward_subs_resolution           true
% 3.26/1.00  --res_backward_subs_resolution          true
% 3.26/1.00  --res_orphan_elimination                true
% 3.26/1.00  --res_time_limit                        2.
% 3.26/1.00  --res_out_proof                         true
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Options
% 3.26/1.00  
% 3.26/1.00  --superposition_flag                    true
% 3.26/1.00  --sup_passive_queue_type                priority_queues
% 3.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.26/1.00  --demod_completeness_check              fast
% 3.26/1.00  --demod_use_ground                      true
% 3.26/1.00  --sup_to_prop_solver                    passive
% 3.26/1.00  --sup_prop_simpl_new                    true
% 3.26/1.00  --sup_prop_simpl_given                  true
% 3.26/1.00  --sup_fun_splitting                     false
% 3.26/1.00  --sup_smt_interval                      50000
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Simplification Setup
% 3.26/1.00  
% 3.26/1.00  --sup_indices_passive                   []
% 3.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_full_bw                           [BwDemod]
% 3.26/1.00  --sup_immed_triv                        [TrivRules]
% 3.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_immed_bw_main                     []
% 3.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  
% 3.26/1.00  ------ Combination Options
% 3.26/1.00  
% 3.26/1.00  --comb_res_mult                         3
% 3.26/1.00  --comb_sup_mult                         2
% 3.26/1.00  --comb_inst_mult                        10
% 3.26/1.00  
% 3.26/1.00  ------ Debug Options
% 3.26/1.00  
% 3.26/1.00  --dbg_backtrace                         false
% 3.26/1.00  --dbg_dump_prop_clauses                 false
% 3.26/1.00  --dbg_dump_prop_clauses_file            -
% 3.26/1.00  --dbg_out_stat                          false
% 3.26/1.00  ------ Parsing...
% 3.26/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/1.00  ------ Proving...
% 3.26/1.00  ------ Problem Properties 
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  clauses                                 24
% 3.26/1.00  conjectures                             5
% 3.26/1.00  EPR                                     6
% 3.26/1.00  Horn                                    11
% 3.26/1.00  unary                                   6
% 3.26/1.00  binary                                  5
% 3.26/1.00  lits                                    88
% 3.26/1.00  lits eq                                 3
% 3.26/1.00  fd_pure                                 0
% 3.26/1.00  fd_pseudo                               0
% 3.26/1.00  fd_cond                                 0
% 3.26/1.00  fd_pseudo_cond                          3
% 3.26/1.00  AC symbols                              0
% 3.26/1.00  
% 3.26/1.00  ------ Schedule dynamic 5 is on 
% 3.26/1.00  
% 3.26/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  ------ 
% 3.26/1.00  Current options:
% 3.26/1.00  ------ 
% 3.26/1.00  
% 3.26/1.00  ------ Input Options
% 3.26/1.00  
% 3.26/1.00  --out_options                           all
% 3.26/1.00  --tptp_safe_out                         true
% 3.26/1.00  --problem_path                          ""
% 3.26/1.00  --include_path                          ""
% 3.26/1.00  --clausifier                            res/vclausify_rel
% 3.26/1.00  --clausifier_options                    --mode clausify
% 3.26/1.00  --stdin                                 false
% 3.26/1.00  --stats_out                             all
% 3.26/1.00  
% 3.26/1.00  ------ General Options
% 3.26/1.00  
% 3.26/1.00  --fof                                   false
% 3.26/1.00  --time_out_real                         305.
% 3.26/1.00  --time_out_virtual                      -1.
% 3.26/1.00  --symbol_type_check                     false
% 3.26/1.00  --clausify_out                          false
% 3.26/1.00  --sig_cnt_out                           false
% 3.26/1.00  --trig_cnt_out                          false
% 3.26/1.00  --trig_cnt_out_tolerance                1.
% 3.26/1.00  --trig_cnt_out_sk_spl                   false
% 3.26/1.00  --abstr_cl_out                          false
% 3.26/1.00  
% 3.26/1.00  ------ Global Options
% 3.26/1.00  
% 3.26/1.00  --schedule                              default
% 3.26/1.00  --add_important_lit                     false
% 3.26/1.00  --prop_solver_per_cl                    1000
% 3.26/1.00  --min_unsat_core                        false
% 3.26/1.00  --soft_assumptions                      false
% 3.26/1.00  --soft_lemma_size                       3
% 3.26/1.00  --prop_impl_unit_size                   0
% 3.26/1.00  --prop_impl_unit                        []
% 3.26/1.00  --share_sel_clauses                     true
% 3.26/1.00  --reset_solvers                         false
% 3.26/1.00  --bc_imp_inh                            [conj_cone]
% 3.26/1.00  --conj_cone_tolerance                   3.
% 3.26/1.00  --extra_neg_conj                        none
% 3.26/1.00  --large_theory_mode                     true
% 3.26/1.00  --prolific_symb_bound                   200
% 3.26/1.00  --lt_threshold                          2000
% 3.26/1.00  --clause_weak_htbl                      true
% 3.26/1.00  --gc_record_bc_elim                     false
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing Options
% 3.26/1.00  
% 3.26/1.00  --preprocessing_flag                    true
% 3.26/1.00  --time_out_prep_mult                    0.1
% 3.26/1.00  --splitting_mode                        input
% 3.26/1.00  --splitting_grd                         true
% 3.26/1.00  --splitting_cvd                         false
% 3.26/1.00  --splitting_cvd_svl                     false
% 3.26/1.00  --splitting_nvd                         32
% 3.26/1.00  --sub_typing                            true
% 3.26/1.00  --prep_gs_sim                           true
% 3.26/1.00  --prep_unflatten                        true
% 3.26/1.00  --prep_res_sim                          true
% 3.26/1.00  --prep_upred                            true
% 3.26/1.00  --prep_sem_filter                       exhaustive
% 3.26/1.00  --prep_sem_filter_out                   false
% 3.26/1.00  --pred_elim                             true
% 3.26/1.00  --res_sim_input                         true
% 3.26/1.00  --eq_ax_congr_red                       true
% 3.26/1.00  --pure_diseq_elim                       true
% 3.26/1.00  --brand_transform                       false
% 3.26/1.00  --non_eq_to_eq                          false
% 3.26/1.00  --prep_def_merge                        true
% 3.26/1.00  --prep_def_merge_prop_impl              false
% 3.26/1.00  --prep_def_merge_mbd                    true
% 3.26/1.00  --prep_def_merge_tr_red                 false
% 3.26/1.00  --prep_def_merge_tr_cl                  false
% 3.26/1.00  --smt_preprocessing                     true
% 3.26/1.00  --smt_ac_axioms                         fast
% 3.26/1.00  --preprocessed_out                      false
% 3.26/1.00  --preprocessed_stats                    false
% 3.26/1.00  
% 3.26/1.00  ------ Abstraction refinement Options
% 3.26/1.00  
% 3.26/1.00  --abstr_ref                             []
% 3.26/1.00  --abstr_ref_prep                        false
% 3.26/1.00  --abstr_ref_until_sat                   false
% 3.26/1.00  --abstr_ref_sig_restrict                funpre
% 3.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/1.00  --abstr_ref_under                       []
% 3.26/1.00  
% 3.26/1.00  ------ SAT Options
% 3.26/1.00  
% 3.26/1.00  --sat_mode                              false
% 3.26/1.00  --sat_fm_restart_options                ""
% 3.26/1.00  --sat_gr_def                            false
% 3.26/1.00  --sat_epr_types                         true
% 3.26/1.00  --sat_non_cyclic_types                  false
% 3.26/1.00  --sat_finite_models                     false
% 3.26/1.00  --sat_fm_lemmas                         false
% 3.26/1.00  --sat_fm_prep                           false
% 3.26/1.00  --sat_fm_uc_incr                        true
% 3.26/1.00  --sat_out_model                         small
% 3.26/1.00  --sat_out_clauses                       false
% 3.26/1.00  
% 3.26/1.00  ------ QBF Options
% 3.26/1.00  
% 3.26/1.00  --qbf_mode                              false
% 3.26/1.00  --qbf_elim_univ                         false
% 3.26/1.00  --qbf_dom_inst                          none
% 3.26/1.00  --qbf_dom_pre_inst                      false
% 3.26/1.00  --qbf_sk_in                             false
% 3.26/1.00  --qbf_pred_elim                         true
% 3.26/1.00  --qbf_split                             512
% 3.26/1.00  
% 3.26/1.00  ------ BMC1 Options
% 3.26/1.00  
% 3.26/1.00  --bmc1_incremental                      false
% 3.26/1.00  --bmc1_axioms                           reachable_all
% 3.26/1.00  --bmc1_min_bound                        0
% 3.26/1.00  --bmc1_max_bound                        -1
% 3.26/1.00  --bmc1_max_bound_default                -1
% 3.26/1.00  --bmc1_symbol_reachability              true
% 3.26/1.00  --bmc1_property_lemmas                  false
% 3.26/1.00  --bmc1_k_induction                      false
% 3.26/1.00  --bmc1_non_equiv_states                 false
% 3.26/1.00  --bmc1_deadlock                         false
% 3.26/1.00  --bmc1_ucm                              false
% 3.26/1.00  --bmc1_add_unsat_core                   none
% 3.26/1.00  --bmc1_unsat_core_children              false
% 3.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/1.00  --bmc1_out_stat                         full
% 3.26/1.00  --bmc1_ground_init                      false
% 3.26/1.00  --bmc1_pre_inst_next_state              false
% 3.26/1.00  --bmc1_pre_inst_state                   false
% 3.26/1.00  --bmc1_pre_inst_reach_state             false
% 3.26/1.00  --bmc1_out_unsat_core                   false
% 3.26/1.00  --bmc1_aig_witness_out                  false
% 3.26/1.00  --bmc1_verbose                          false
% 3.26/1.00  --bmc1_dump_clauses_tptp                false
% 3.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.26/1.00  --bmc1_dump_file                        -
% 3.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.26/1.00  --bmc1_ucm_extend_mode                  1
% 3.26/1.00  --bmc1_ucm_init_mode                    2
% 3.26/1.00  --bmc1_ucm_cone_mode                    none
% 3.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.26/1.00  --bmc1_ucm_relax_model                  4
% 3.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/1.00  --bmc1_ucm_layered_model                none
% 3.26/1.00  --bmc1_ucm_max_lemma_size               10
% 3.26/1.00  
% 3.26/1.00  ------ AIG Options
% 3.26/1.00  
% 3.26/1.00  --aig_mode                              false
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation Options
% 3.26/1.00  
% 3.26/1.00  --instantiation_flag                    true
% 3.26/1.00  --inst_sos_flag                         false
% 3.26/1.00  --inst_sos_phase                        true
% 3.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/1.00  --inst_lit_sel_side                     none
% 3.26/1.00  --inst_solver_per_active                1400
% 3.26/1.00  --inst_solver_calls_frac                1.
% 3.26/1.00  --inst_passive_queue_type               priority_queues
% 3.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/1.00  --inst_passive_queues_freq              [25;2]
% 3.26/1.00  --inst_dismatching                      true
% 3.26/1.00  --inst_eager_unprocessed_to_passive     true
% 3.26/1.00  --inst_prop_sim_given                   true
% 3.26/1.00  --inst_prop_sim_new                     false
% 3.26/1.00  --inst_subs_new                         false
% 3.26/1.00  --inst_eq_res_simp                      false
% 3.26/1.00  --inst_subs_given                       false
% 3.26/1.00  --inst_orphan_elimination               true
% 3.26/1.00  --inst_learning_loop_flag               true
% 3.26/1.00  --inst_learning_start                   3000
% 3.26/1.00  --inst_learning_factor                  2
% 3.26/1.00  --inst_start_prop_sim_after_learn       3
% 3.26/1.00  --inst_sel_renew                        solver
% 3.26/1.00  --inst_lit_activity_flag                true
% 3.26/1.00  --inst_restr_to_given                   false
% 3.26/1.00  --inst_activity_threshold               500
% 3.26/1.00  --inst_out_proof                        true
% 3.26/1.00  
% 3.26/1.00  ------ Resolution Options
% 3.26/1.00  
% 3.26/1.00  --resolution_flag                       false
% 3.26/1.00  --res_lit_sel                           adaptive
% 3.26/1.00  --res_lit_sel_side                      none
% 3.26/1.00  --res_ordering                          kbo
% 3.26/1.00  --res_to_prop_solver                    active
% 3.26/1.00  --res_prop_simpl_new                    false
% 3.26/1.00  --res_prop_simpl_given                  true
% 3.26/1.00  --res_passive_queue_type                priority_queues
% 3.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/1.00  --res_passive_queues_freq               [15;5]
% 3.26/1.00  --res_forward_subs                      full
% 3.26/1.00  --res_backward_subs                     full
% 3.26/1.00  --res_forward_subs_resolution           true
% 3.26/1.00  --res_backward_subs_resolution          true
% 3.26/1.00  --res_orphan_elimination                true
% 3.26/1.00  --res_time_limit                        2.
% 3.26/1.00  --res_out_proof                         true
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Options
% 3.26/1.00  
% 3.26/1.00  --superposition_flag                    true
% 3.26/1.00  --sup_passive_queue_type                priority_queues
% 3.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.26/1.00  --demod_completeness_check              fast
% 3.26/1.00  --demod_use_ground                      true
% 3.26/1.00  --sup_to_prop_solver                    passive
% 3.26/1.00  --sup_prop_simpl_new                    true
% 3.26/1.00  --sup_prop_simpl_given                  true
% 3.26/1.00  --sup_fun_splitting                     false
% 3.26/1.00  --sup_smt_interval                      50000
% 3.26/1.00  
% 3.26/1.00  ------ Superposition Simplification Setup
% 3.26/1.00  
% 3.26/1.00  --sup_indices_passive                   []
% 3.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_full_bw                           [BwDemod]
% 3.26/1.00  --sup_immed_triv                        [TrivRules]
% 3.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_immed_bw_main                     []
% 3.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/1.00  
% 3.26/1.00  ------ Combination Options
% 3.26/1.00  
% 3.26/1.00  --comb_res_mult                         3
% 3.26/1.00  --comb_sup_mult                         2
% 3.26/1.00  --comb_inst_mult                        10
% 3.26/1.00  
% 3.26/1.00  ------ Debug Options
% 3.26/1.00  
% 3.26/1.00  --dbg_backtrace                         false
% 3.26/1.00  --dbg_dump_prop_clauses                 false
% 3.26/1.00  --dbg_dump_prop_clauses_file            -
% 3.26/1.00  --dbg_out_stat                          false
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  ------ Proving...
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  % SZS status Theorem for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00   Resolution empty clause
% 3.26/1.00  
% 3.26/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  fof(f1,axiom,(
% 3.26/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f11,plain,(
% 3.26/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.26/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.26/1.00  
% 3.26/1.00  fof(f14,plain,(
% 3.26/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.26/1.00    inference(ennf_transformation,[],[f11])).
% 3.26/1.00  
% 3.26/1.00  fof(f24,plain,(
% 3.26/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f25,plain,(
% 3.26/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f24])).
% 3.26/1.00  
% 3.26/1.00  fof(f44,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f25])).
% 3.26/1.00  
% 3.26/1.00  fof(f3,axiom,(
% 3.26/1.00    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f15,plain,(
% 3.26/1.00    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.26/1.00    inference(ennf_transformation,[],[f3])).
% 3.26/1.00  
% 3.26/1.00  fof(f31,plain,(
% 3.26/1.00    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f32,plain,(
% 3.26/1.00    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f31])).
% 3.26/1.00  
% 3.26/1.00  fof(f52,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X0,X1)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f32])).
% 3.26/1.00  
% 3.26/1.00  fof(f2,axiom,(
% 3.26/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f26,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.26/1.00    inference(nnf_transformation,[],[f2])).
% 3.26/1.00  
% 3.26/1.00  fof(f27,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.26/1.00    inference(flattening,[],[f26])).
% 3.26/1.00  
% 3.26/1.00  fof(f28,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.26/1.00    inference(rectify,[],[f27])).
% 3.26/1.00  
% 3.26/1.00  fof(f29,plain,(
% 3.26/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f30,plain,(
% 3.26/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.26/1.00  
% 3.26/1.00  fof(f46,plain,(
% 3.26/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.26/1.00    inference(cnf_transformation,[],[f30])).
% 3.26/1.00  
% 3.26/1.00  fof(f5,axiom,(
% 3.26/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f55,plain,(
% 3.26/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f5])).
% 3.26/1.00  
% 3.26/1.00  fof(f75,plain,(
% 3.26/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 3.26/1.00    inference(definition_unfolding,[],[f46,f55])).
% 3.26/1.00  
% 3.26/1.00  fof(f78,plain,(
% 3.26/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 3.26/1.00    inference(equality_resolution,[],[f75])).
% 3.26/1.00  
% 3.26/1.00  fof(f9,conjecture,(
% 3.26/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f10,negated_conjecture,(
% 3.26/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.26/1.00    inference(negated_conjecture,[],[f9])).
% 3.26/1.00  
% 3.26/1.00  fof(f12,plain,(
% 3.26/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.26/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.26/1.00  
% 3.26/1.00  fof(f13,plain,(
% 3.26/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 3.26/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.26/1.00  
% 3.26/1.00  fof(f22,plain,(
% 3.26/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.26/1.00    inference(ennf_transformation,[],[f13])).
% 3.26/1.00  
% 3.26/1.00  fof(f23,plain,(
% 3.26/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.26/1.00    inference(flattening,[],[f22])).
% 3.26/1.00  
% 3.26/1.00  fof(f42,plain,(
% 3.26/1.00    ( ! [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (~r1_waybel_0(X0,sK7,u1_struct_0(X0)) & l1_waybel_0(sK7,X0) & ~v2_struct_0(sK7))) )),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f41,plain,(
% 3.26/1.00    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK6,X1,u1_struct_0(sK6)) & l1_waybel_0(X1,sK6) & ~v2_struct_0(X1)) & l1_struct_0(sK6) & ~v2_struct_0(sK6))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f43,plain,(
% 3.26/1.00    (~r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) & l1_waybel_0(sK7,sK6) & ~v2_struct_0(sK7)) & l1_struct_0(sK6) & ~v2_struct_0(sK6)),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f42,f41])).
% 3.26/1.00  
% 3.26/1.00  fof(f65,plain,(
% 3.26/1.00    ~v2_struct_0(sK6)),
% 3.26/1.00    inference(cnf_transformation,[],[f43])).
% 3.26/1.00  
% 3.26/1.00  fof(f66,plain,(
% 3.26/1.00    l1_struct_0(sK6)),
% 3.26/1.00    inference(cnf_transformation,[],[f43])).
% 3.26/1.00  
% 3.26/1.00  fof(f67,plain,(
% 3.26/1.00    ~v2_struct_0(sK7)),
% 3.26/1.00    inference(cnf_transformation,[],[f43])).
% 3.26/1.00  
% 3.26/1.00  fof(f68,plain,(
% 3.26/1.00    l1_waybel_0(sK7,sK6)),
% 3.26/1.00    inference(cnf_transformation,[],[f43])).
% 3.26/1.00  
% 3.26/1.00  fof(f69,plain,(
% 3.26/1.00    ~r1_waybel_0(sK6,sK7,u1_struct_0(sK6))),
% 3.26/1.00    inference(cnf_transformation,[],[f43])).
% 3.26/1.00  
% 3.26/1.00  fof(f7,axiom,(
% 3.26/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f18,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.26/1.00    inference(ennf_transformation,[],[f7])).
% 3.26/1.00  
% 3.26/1.00  fof(f19,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.26/1.00    inference(flattening,[],[f18])).
% 3.26/1.00  
% 3.26/1.00  fof(f40,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.26/1.00    inference(nnf_transformation,[],[f19])).
% 3.26/1.00  
% 3.26/1.00  fof(f62,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f40])).
% 3.26/1.00  
% 3.26/1.00  fof(f4,axiom,(
% 3.26/1.00    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f33,plain,(
% 3.26/1.00    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f34,plain,(
% 3.26/1.00    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f4,f33])).
% 3.26/1.00  
% 3.26/1.00  fof(f54,plain,(
% 3.26/1.00    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f34])).
% 3.26/1.00  
% 3.26/1.00  fof(f6,axiom,(
% 3.26/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f16,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.26/1.00    inference(ennf_transformation,[],[f6])).
% 3.26/1.00  
% 3.26/1.00  fof(f17,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.26/1.00    inference(flattening,[],[f16])).
% 3.26/1.00  
% 3.26/1.00  fof(f35,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.26/1.00    inference(nnf_transformation,[],[f17])).
% 3.26/1.00  
% 3.26/1.00  fof(f36,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.26/1.00    inference(rectify,[],[f35])).
% 3.26/1.00  
% 3.26/1.00  fof(f38,plain,(
% 3.26/1.00    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5)) & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f37,plain,(
% 3.26/1.00    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK4(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 3.26/1.00    introduced(choice_axiom,[])).
% 3.26/1.00  
% 3.26/1.00  fof(f39,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK4(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5)) & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.26/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f38,f37])).
% 3.26/1.00  
% 3.26/1.00  fof(f58,plain,(
% 3.26/1.00    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f39])).
% 3.26/1.00  
% 3.26/1.00  fof(f8,axiom,(
% 3.26/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 3.26/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.26/1.00  
% 3.26/1.00  fof(f20,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.26/1.00    inference(ennf_transformation,[],[f8])).
% 3.26/1.00  
% 3.26/1.00  fof(f21,plain,(
% 3.26/1.00    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.26/1.00    inference(flattening,[],[f20])).
% 3.26/1.00  
% 3.26/1.00  fof(f63,plain,(
% 3.26/1.00    ( ! [X2,X0,X3,X1] : (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2) | ~r1_tarski(X2,X3) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f21])).
% 3.26/1.00  
% 3.26/1.00  fof(f45,plain,(
% 3.26/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f25])).
% 3.26/1.00  
% 3.26/1.00  fof(f49,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f30])).
% 3.26/1.00  
% 3.26/1.00  fof(f72,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.26/1.00    inference(definition_unfolding,[],[f49,f55])).
% 3.26/1.00  
% 3.26/1.00  fof(f50,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.26/1.00    inference(cnf_transformation,[],[f30])).
% 3.26/1.00  
% 3.26/1.00  fof(f71,plain,(
% 3.26/1.00    ( ! [X2,X0,X1] : (k6_subset_1(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.26/1.00    inference(definition_unfolding,[],[f50,f55])).
% 3.26/1.00  
% 3.26/1.00  fof(f47,plain,(
% 3.26/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.26/1.00    inference(cnf_transformation,[],[f30])).
% 3.26/1.00  
% 3.26/1.00  fof(f74,plain,(
% 3.26/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 3.26/1.00    inference(definition_unfolding,[],[f47,f55])).
% 3.26/1.00  
% 3.26/1.00  fof(f77,plain,(
% 3.26/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 3.26/1.00    inference(equality_resolution,[],[f74])).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1,plain,
% 3.26/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1212,plain,
% 3.26/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.26/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_9,plain,
% 3.26/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1204,plain,
% 3.26/1.00      ( r2_hidden(X0,X1) != iProver_top | r2_hidden(sK2(X1),X1) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1587,plain,
% 3.26/1.00      ( r2_hidden(sK2(X0),X0) = iProver_top | r1_tarski(X0,X1) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1212,c_1204]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7,plain,
% 3.26/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1206,plain,
% 3.26/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.26/1.00      | r2_hidden(X0,k6_subset_1(X1,X2)) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1985,plain,
% 3.26/1.00      ( r2_hidden(sK2(k6_subset_1(X0,X1)),X0) = iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1587,c_1206]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2119,plain,
% 3.26/1.00      ( r2_hidden(sK2(X0),X0) = iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1985,c_1204]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2560,plain,
% 3.26/1.00      ( r2_hidden(sK2(k6_subset_1(X0,X1)),X0) = iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X3) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_2119,c_1206]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4985,plain,
% 3.26/1.00      ( r2_hidden(sK2(X0),X0) = iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X3) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_2560,c_1204]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_5143,plain,
% 3.26/1.00      ( r2_hidden(sK2(k6_subset_1(X0,X1)),X0) = iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_4985,c_1206]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11095,plain,
% 3.26/1.00      ( r2_hidden(sK2(X0),X0) = iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_5143,c_1204]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_24,negated_conjecture,
% 3.26/1.00      ( ~ v2_struct_0(sK6) ),
% 3.26/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_25,plain,
% 3.26/1.00      ( v2_struct_0(sK6) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_23,negated_conjecture,
% 3.26/1.00      ( l1_struct_0(sK6) ),
% 3.26/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_26,plain,
% 3.26/1.00      ( l1_struct_0(sK6) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_22,negated_conjecture,
% 3.26/1.00      ( ~ v2_struct_0(sK7) ),
% 3.26/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_27,plain,
% 3.26/1.00      ( v2_struct_0(sK7) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_21,negated_conjecture,
% 3.26/1.00      ( l1_waybel_0(sK7,sK6) ),
% 3.26/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_28,plain,
% 3.26/1.00      ( l1_waybel_0(sK7,sK6) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_20,negated_conjecture,
% 3.26/1.00      ( ~ r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_29,plain,
% 3.26/1.00      ( r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_16,plain,
% 3.26/1.00      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
% 3.26/1.00      | r2_waybel_0(X0,X1,X2)
% 3.26/1.00      | ~ l1_waybel_0(X1,X0)
% 3.26/1.00      | ~ l1_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1458,plain,
% 3.26/1.00      ( r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X0))
% 3.26/1.00      | r2_waybel_0(sK6,sK7,X0)
% 3.26/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.26/1.00      | ~ l1_struct_0(sK6)
% 3.26/1.00      | v2_struct_0(sK7)
% 3.26/1.00      | v2_struct_0(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1459,plain,
% 3.26/1.00      ( r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X0)) = iProver_top
% 3.26/1.00      | r2_waybel_0(sK6,sK7,X0) = iProver_top
% 3.26/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.26/1.00      | l1_struct_0(sK6) != iProver_top
% 3.26/1.00      | v2_struct_0(sK7) = iProver_top
% 3.26/1.00      | v2_struct_0(sK6) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_10,plain,
% 3.26/1.00      ( m1_subset_1(sK3(X0),X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1531,plain,
% 3.26/1.00      ( m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1536,plain,
% 3.26/1.00      ( m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_1531]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_13,plain,
% 3.26/1.00      ( ~ r2_waybel_0(X0,X1,X2)
% 3.26/1.00      | ~ l1_waybel_0(X1,X0)
% 3.26/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 3.26/1.00      | r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X3)),X2)
% 3.26/1.00      | ~ l1_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1479,plain,
% 3.26/1.00      ( ~ r2_waybel_0(sK6,sK7,X0)
% 3.26/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.26/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.26/1.00      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,X1)),X0)
% 3.26/1.00      | ~ l1_struct_0(sK6)
% 3.26/1.00      | v2_struct_0(sK7)
% 3.26/1.00      | v2_struct_0(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1567,plain,
% 3.26/1.00      ( ~ r2_waybel_0(sK6,sK7,X0)
% 3.26/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.26/1.00      | ~ m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7))
% 3.26/1.00      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(u1_struct_0(sK7)))),X0)
% 3.26/1.00      | ~ l1_struct_0(sK6)
% 3.26/1.00      | v2_struct_0(sK7)
% 3.26/1.00      | v2_struct_0(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1479]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1569,plain,
% 3.26/1.00      ( r2_waybel_0(sK6,sK7,X0) != iProver_top
% 3.26/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.26/1.00      | m1_subset_1(sK3(u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top
% 3.26/1.00      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(u1_struct_0(sK7)))),X0) = iProver_top
% 3.26/1.00      | l1_struct_0(sK6) != iProver_top
% 3.26/1.00      | v2_struct_0(sK7) = iProver_top
% 3.26/1.00      | v2_struct_0(sK6) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_19,plain,
% 3.26/1.00      ( ~ r1_waybel_0(X0,X1,X2)
% 3.26/1.00      | r1_waybel_0(X0,X1,X3)
% 3.26/1.00      | ~ l1_waybel_0(X1,X0)
% 3.26/1.00      | ~ r1_tarski(X2,X3)
% 3.26/1.00      | ~ l1_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1471,plain,
% 3.26/1.00      ( ~ r1_waybel_0(sK6,sK7,X0)
% 3.26/1.00      | r1_waybel_0(sK6,sK7,X1)
% 3.26/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.26/1.00      | ~ r1_tarski(X0,X1)
% 3.26/1.00      | ~ l1_struct_0(sK6)
% 3.26/1.00      | v2_struct_0(sK7)
% 3.26/1.00      | v2_struct_0(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1678,plain,
% 3.26/1.00      ( r1_waybel_0(sK6,sK7,X0)
% 3.26/1.00      | ~ r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X1))
% 3.26/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.26/1.00      | ~ r1_tarski(k6_subset_1(u1_struct_0(sK6),X1),X0)
% 3.26/1.00      | ~ l1_struct_0(sK6)
% 3.26/1.00      | v2_struct_0(sK7)
% 3.26/1.00      | v2_struct_0(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1471]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2545,plain,
% 3.26/1.00      ( ~ r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X0))
% 3.26/1.00      | r1_waybel_0(sK6,sK7,u1_struct_0(sK6))
% 3.26/1.00      | ~ l1_waybel_0(sK7,sK6)
% 3.26/1.00      | ~ r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6))
% 3.26/1.00      | ~ l1_struct_0(sK6)
% 3.26/1.00      | v2_struct_0(sK7)
% 3.26/1.00      | v2_struct_0(sK6) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1678]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2546,plain,
% 3.26/1.00      ( r1_waybel_0(sK6,sK7,k6_subset_1(u1_struct_0(sK6),X0)) != iProver_top
% 3.26/1.00      | r1_waybel_0(sK6,sK7,u1_struct_0(sK6)) = iProver_top
% 3.26/1.00      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) != iProver_top
% 3.26/1.00      | l1_struct_0(sK6) != iProver_top
% 3.26/1.00      | v2_struct_0(sK7) = iProver_top
% 3.26/1.00      | v2_struct_0(sK6) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2545]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1956,plain,
% 3.26/1.00      ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),X1),k6_subset_1(u1_struct_0(sK6),X0))
% 3.26/1.00      | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),X1) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2922,plain,
% 3.26/1.00      ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),k6_subset_1(u1_struct_0(sK6),X0))
% 3.26/1.00      | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1956]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2923,plain,
% 3.26/1.00      ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),k6_subset_1(u1_struct_0(sK6),X0)) = iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2922]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_0,plain,
% 3.26/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1957,plain,
% 3.26/1.00      ( ~ r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),X1),X1)
% 3.26/1.00      | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),X1) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2921,plain,
% 3.26/1.00      ( ~ r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),u1_struct_0(sK6))
% 3.26/1.00      | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_1957]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2927,plain,
% 3.26/1.00      ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),u1_struct_0(sK6)) != iProver_top
% 3.26/1.00      | r1_tarski(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_2921]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3951,plain,
% 3.26/1.00      ( ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(u1_struct_0(sK7)))),X0)
% 3.26/1.00      | r2_hidden(sK2(X0),X0) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3952,plain,
% 3.26/1.00      ( r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK6,sK7,X0,sK3(u1_struct_0(sK7)))),X0) != iProver_top
% 3.26/1.00      | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3951]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7091,plain,
% 3.26/1.00      ( ~ r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),k6_subset_1(u1_struct_0(sK6),X0))
% 3.26/1.00      | r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),u1_struct_0(sK6)) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7092,plain,
% 3.26/1.00      ( r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),k6_subset_1(u1_struct_0(sK6),X0)) != iProver_top
% 3.26/1.00      | r2_hidden(sK0(k6_subset_1(u1_struct_0(sK6),X0),u1_struct_0(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_7091]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11371,plain,
% 3.26/1.00      ( r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_11095,c_25,c_26,c_27,c_28,c_29,c_1459,c_1536,c_1569,
% 3.26/1.00                 c_2546,c_2923,c_2927,c_3952,c_7092]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4,plain,
% 3.26/1.00      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.26/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.26/1.00      | k6_subset_1(X0,X1) = X2 ),
% 3.26/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1209,plain,
% 3.26/1.00      ( k6_subset_1(X0,X1) = X2
% 3.26/1.00      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 3.26/1.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3,plain,
% 3.26/1.00      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 3.26/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.26/1.00      | k6_subset_1(X0,X1) = X2 ),
% 3.26/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1210,plain,
% 3.26/1.00      ( k6_subset_1(X0,X1) = X2
% 3.26/1.00      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 3.26/1.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2282,plain,
% 3.26/1.00      ( k6_subset_1(X0,X0) = X1 | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1209,c_1210]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3504,plain,
% 3.26/1.00      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
% 3.26/1.00      | r2_hidden(sK1(X0,X0,k6_subset_1(X1,X2)),X1) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_2282,c_1206]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6,plain,
% 3.26/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1207,plain,
% 3.26/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.26/1.00      | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3505,plain,
% 3.26/1.00      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X2)
% 3.26/1.00      | r2_hidden(sK1(X0,X0,k6_subset_1(X1,X2)),X2) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_2282,c_1207]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6424,plain,
% 3.26/1.00      ( k6_subset_1(X0,X0) = k6_subset_1(X1,X1) ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_3504,c_3505]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7289,plain,
% 3.26/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.26/1.00      | r2_hidden(X0,k6_subset_1(X2,X2)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_6424,c_1206]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7290,plain,
% 3.26/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.26/1.00      | r2_hidden(X0,k6_subset_1(X2,X2)) != iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_6424,c_1207]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7416,plain,
% 3.26/1.00      ( r2_hidden(X0,k6_subset_1(X1,X1)) != iProver_top ),
% 3.26/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_7289,c_7290]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_11382,plain,
% 3.26/1.00      ( $false ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_11371,c_7416]) ).
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  ------                               Statistics
% 3.26/1.00  
% 3.26/1.00  ------ General
% 3.26/1.00  
% 3.26/1.00  abstr_ref_over_cycles:                  0
% 3.26/1.00  abstr_ref_under_cycles:                 0
% 3.26/1.00  gc_basic_clause_elim:                   0
% 3.26/1.00  forced_gc_time:                         0
% 3.26/1.00  parsing_time:                           0.013
% 3.26/1.00  unif_index_cands_time:                  0.
% 3.26/1.00  unif_index_add_time:                    0.
% 3.26/1.00  orderings_time:                         0.
% 3.26/1.00  out_proof_time:                         0.012
% 3.26/1.00  total_time:                             0.314
% 3.26/1.00  num_of_symbols:                         51
% 3.26/1.00  num_of_terms:                           13034
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing
% 3.26/1.00  
% 3.26/1.00  num_of_splits:                          0
% 3.26/1.00  num_of_split_atoms:                     0
% 3.26/1.00  num_of_reused_defs:                     0
% 3.26/1.00  num_eq_ax_congr_red:                    65
% 3.26/1.00  num_of_sem_filtered_clauses:            1
% 3.26/1.00  num_of_subtypes:                        0
% 3.26/1.00  monotx_restored_types:                  0
% 3.26/1.00  sat_num_of_epr_types:                   0
% 3.26/1.00  sat_num_of_non_cyclic_types:            0
% 3.26/1.00  sat_guarded_non_collapsed_types:        0
% 3.26/1.00  num_pure_diseq_elim:                    0
% 3.26/1.00  simp_replaced_by:                       0
% 3.26/1.00  res_preprocessed:                       122
% 3.26/1.00  prep_upred:                             0
% 3.26/1.00  prep_unflattend:                        19
% 3.26/1.00  smt_new_axioms:                         0
% 3.26/1.00  pred_elim_cands:                        8
% 3.26/1.00  pred_elim:                              1
% 3.26/1.00  pred_elim_cl:                           1
% 3.26/1.00  pred_elim_cycles:                       3
% 3.26/1.00  merged_defs:                            0
% 3.26/1.00  merged_defs_ncl:                        0
% 3.26/1.00  bin_hyper_res:                          0
% 3.26/1.00  prep_cycles:                            4
% 3.26/1.00  pred_elim_time:                         0.005
% 3.26/1.00  splitting_time:                         0.
% 3.26/1.00  sem_filter_time:                        0.
% 3.26/1.00  monotx_time:                            0.
% 3.26/1.00  subtype_inf_time:                       0.
% 3.26/1.00  
% 3.26/1.00  ------ Problem properties
% 3.26/1.00  
% 3.26/1.00  clauses:                                24
% 3.26/1.00  conjectures:                            5
% 3.26/1.00  epr:                                    6
% 3.26/1.00  horn:                                   11
% 3.26/1.00  ground:                                 5
% 3.26/1.00  unary:                                  6
% 3.26/1.00  binary:                                 5
% 3.26/1.00  lits:                                   88
% 3.26/1.00  lits_eq:                                3
% 3.26/1.00  fd_pure:                                0
% 3.26/1.00  fd_pseudo:                              0
% 3.26/1.00  fd_cond:                                0
% 3.26/1.00  fd_pseudo_cond:                         3
% 3.26/1.00  ac_symbols:                             0
% 3.26/1.00  
% 3.26/1.00  ------ Propositional Solver
% 3.26/1.00  
% 3.26/1.00  prop_solver_calls:                      29
% 3.26/1.00  prop_fast_solver_calls:                 1198
% 3.26/1.00  smt_solver_calls:                       0
% 3.26/1.00  smt_fast_solver_calls:                  0
% 3.26/1.00  prop_num_of_clauses:                    3760
% 3.26/1.00  prop_preprocess_simplified:             10058
% 3.26/1.00  prop_fo_subsumed:                       1
% 3.26/1.00  prop_solver_time:                       0.
% 3.26/1.00  smt_solver_time:                        0.
% 3.26/1.00  smt_fast_solver_time:                   0.
% 3.26/1.00  prop_fast_solver_time:                  0.
% 3.26/1.00  prop_unsat_core_time:                   0.
% 3.26/1.00  
% 3.26/1.00  ------ QBF
% 3.26/1.00  
% 3.26/1.00  qbf_q_res:                              0
% 3.26/1.00  qbf_num_tautologies:                    0
% 3.26/1.00  qbf_prep_cycles:                        0
% 3.26/1.00  
% 3.26/1.00  ------ BMC1
% 3.26/1.00  
% 3.26/1.00  bmc1_current_bound:                     -1
% 3.26/1.00  bmc1_last_solved_bound:                 -1
% 3.26/1.00  bmc1_unsat_core_size:                   -1
% 3.26/1.00  bmc1_unsat_core_parents_size:           -1
% 3.26/1.00  bmc1_merge_next_fun:                    0
% 3.26/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation
% 3.26/1.00  
% 3.26/1.00  inst_num_of_clauses:                    1016
% 3.26/1.00  inst_num_in_passive:                    265
% 3.26/1.00  inst_num_in_active:                     378
% 3.26/1.00  inst_num_in_unprocessed:                373
% 3.26/1.00  inst_num_of_loops:                      500
% 3.26/1.00  inst_num_of_learning_restarts:          0
% 3.26/1.00  inst_num_moves_active_passive:          118
% 3.26/1.00  inst_lit_activity:                      0
% 3.26/1.00  inst_lit_activity_moves:                0
% 3.26/1.00  inst_num_tautologies:                   0
% 3.26/1.00  inst_num_prop_implied:                  0
% 3.26/1.00  inst_num_existing_simplified:           0
% 3.26/1.00  inst_num_eq_res_simplified:             0
% 3.26/1.00  inst_num_child_elim:                    0
% 3.26/1.00  inst_num_of_dismatching_blockings:      587
% 3.26/1.00  inst_num_of_non_proper_insts:           710
% 3.26/1.00  inst_num_of_duplicates:                 0
% 3.26/1.00  inst_inst_num_from_inst_to_res:         0
% 3.26/1.00  inst_dismatching_checking_time:         0.
% 3.26/1.00  
% 3.26/1.00  ------ Resolution
% 3.26/1.00  
% 3.26/1.00  res_num_of_clauses:                     0
% 3.26/1.00  res_num_in_passive:                     0
% 3.26/1.00  res_num_in_active:                      0
% 3.26/1.00  res_num_of_loops:                       126
% 3.26/1.00  res_forward_subset_subsumed:            70
% 3.26/1.00  res_backward_subset_subsumed:           8
% 3.26/1.00  res_forward_subsumed:                   0
% 3.26/1.00  res_backward_subsumed:                  0
% 3.26/1.00  res_forward_subsumption_resolution:     2
% 3.26/1.00  res_backward_subsumption_resolution:    0
% 3.26/1.00  res_clause_to_clause_subsumption:       2480
% 3.26/1.00  res_orphan_elimination:                 0
% 3.26/1.00  res_tautology_del:                      140
% 3.26/1.00  res_num_eq_res_simplified:              0
% 3.26/1.00  res_num_sel_changes:                    0
% 3.26/1.00  res_moves_from_active_to_pass:          0
% 3.26/1.00  
% 3.26/1.00  ------ Superposition
% 3.26/1.00  
% 3.26/1.00  sup_time_total:                         0.
% 3.26/1.00  sup_time_generating:                    0.
% 3.26/1.00  sup_time_sim_full:                      0.
% 3.26/1.00  sup_time_sim_immed:                     0.
% 3.26/1.00  
% 3.26/1.00  sup_num_of_clauses:                     215
% 3.26/1.00  sup_num_in_active:                      92
% 3.26/1.00  sup_num_in_passive:                     123
% 3.26/1.00  sup_num_of_loops:                       98
% 3.26/1.00  sup_fw_superposition:                   378
% 3.26/1.00  sup_bw_superposition:                   576
% 3.26/1.00  sup_immediate_simplified:               363
% 3.26/1.00  sup_given_eliminated:                   4
% 3.26/1.00  comparisons_done:                       0
% 3.26/1.00  comparisons_avoided:                    0
% 3.26/1.00  
% 3.26/1.00  ------ Simplifications
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  sim_fw_subset_subsumed:                 119
% 3.26/1.00  sim_bw_subset_subsumed:                 27
% 3.26/1.00  sim_fw_subsumed:                        100
% 3.26/1.00  sim_bw_subsumed:                        17
% 3.26/1.00  sim_fw_subsumption_res:                 4
% 3.26/1.00  sim_bw_subsumption_res:                 0
% 3.26/1.00  sim_tautology_del:                      13
% 3.26/1.00  sim_eq_tautology_del:                   20
% 3.26/1.00  sim_eq_res_simp:                        1
% 3.26/1.00  sim_fw_demodulated:                     120
% 3.26/1.00  sim_bw_demodulated:                     6
% 3.26/1.00  sim_light_normalised:                   97
% 3.26/1.00  sim_joinable_taut:                      0
% 3.26/1.00  sim_joinable_simp:                      0
% 3.26/1.00  sim_ac_normalised:                      0
% 3.26/1.00  sim_smt_subsumption:                    0
% 3.26/1.00  
%------------------------------------------------------------------------------
