%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:53 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 514 expanded)
%              Number of clauses        :   61 ( 103 expanded)
%              Number of leaves         :   14 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :  532 (3793 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ? [X6] :
                      ( r1_orders_2(X0,X5,X6)
                      & r1_orders_2(X0,X4,X6)
                      & m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f22])).

fof(f26,plain,(
    ! [X5,X4,X0] :
      ( ? [X6] :
          ( r1_orders_2(X0,X5,X6)
          & r1_orders_2(X0,X4,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X5,sK4(X0,X4,X5))
        & r1_orders_2(X0,X4,sK4(X0,X4,X5))
        & m1_subset_1(sK4(X0,X4,X5),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_orders_2(X0,sK3(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK2(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ( ! [X3] :
                ( ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ r1_orders_2(X0,sK2(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ( r1_orders_2(X0,X5,sK4(X0,X4,X5))
                    & r1_orders_2(X0,X4,sK4(X0,X4,X5))
                    & m1_subset_1(sK4(X0,X4,X5),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f40,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK4(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ~ ( r1_xboole_0(X2,X3)
                  & r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( r1_xboole_0(X2,X3)
          & r1_waybel_0(X0,X1,X3)
          & r1_waybel_0(X0,X1,X2) )
     => ( r1_xboole_0(sK8,sK9)
        & r1_waybel_0(X0,X1,sK9)
        & r1_waybel_0(X0,X1,sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X3,X2] :
            ( r1_xboole_0(X2,X3)
            & r1_waybel_0(X0,sK7,X3)
            & r1_waybel_0(X0,sK7,X2) )
        & l1_waybel_0(sK7,X0)
        & v7_waybel_0(sK7)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(sK6,X1,X3)
              & r1_waybel_0(sK6,X1,X2) )
          & l1_waybel_0(X1,sK6)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( r1_xboole_0(sK8,sK9)
    & r1_waybel_0(sK6,sK7,sK9)
    & r1_waybel_0(sK6,sK7,sK8)
    & l1_waybel_0(sK7,sK6)
    & v7_waybel_0(sK7)
    & ~ v2_struct_0(sK7)
    & l1_struct_0(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f32,f31,f30])).

fof(f53,plain,(
    l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f17])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
        & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3))
                      & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f35,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

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
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f14,f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK4(X0,X4,X5),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK4(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    r1_waybel_0(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f33])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    r1_waybel_0(sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    r1_xboole_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( r1_orders_2(X0,X1,sK4(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_357,plain,
    ( l1_orders_2(sK7)
    | ~ l1_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_11,c_18])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_359,plain,
    ( l1_orders_2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_21])).

cnf(c_412,plain,
    ( r1_orders_2(sK7,X0,sK4(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v7_waybel_0(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_9,c_359])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_416,plain,
    ( r1_orders_2(sK7,X0,sK4(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_20,c_19])).

cnf(c_1091,plain,
    ( r1_orders_2(sK7,X0_50,sK4(sK7,X0_50,X1_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_1184,plain,
    ( r1_orders_2(sK7,sK1(sK6,sK7,X0_54),sK4(sK7,sK1(sK6,sK7,X0_54),X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,X0_54),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_1532,plain,
    ( r1_orders_2(sK7,sK1(sK6,sK7,X0_54),sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,X1_54)))
    | ~ m1_subset_1(sK1(sK6,sK7,X0_54),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,X1_54),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1184])).

cnf(c_11123,plain,
    ( r1_orders_2(sK7,sK1(sK6,sK7,sK8),sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9)))
    | ~ m1_subset_1(sK1(sK6,sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,sK1(X1,X0,X2),X3)
    | ~ r1_waybel_0(X1,X0,X2)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(k2_waybel_0(X1,X0,X3),X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_367,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,X0),X1)
    | ~ r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,X1),X0)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_3,c_18])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_371,plain,
    ( r2_hidden(k2_waybel_0(sK6,sK7,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r1_waybel_0(sK6,sK7,X0)
    | ~ r1_orders_2(sK7,sK1(sK6,sK7,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_22,c_21,c_20])).

cnf(c_372,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,X0),X1)
    | ~ r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,X1),X0) ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_1092,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,X0_54),X0_50)
    | ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,X0_50),X0_54) ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_1192,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,X0_54),sK4(sK7,X0_50,sK1(sK6,sK7,X1_54)))
    | ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(sK4(sK7,X0_50,sK1(sK6,sK7,X1_54)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,X0_50,sK1(sK6,sK7,X1_54))),X0_54) ),
    inference(instantiation,[status(thm)],[c_1092])).

cnf(c_1295,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,X0_54),sK4(sK7,sK1(sK6,sK7,X1_54),sK1(sK6,sK7,X2_54)))
    | ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(sK4(sK7,sK1(sK6,sK7,X1_54),sK1(sK6,sK7,X2_54)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X1_54),sK1(sK6,sK7,X2_54))),X0_54) ),
    inference(instantiation,[status(thm)],[c_1192])).

cnf(c_9074,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,sK8),sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9)))
    | ~ r1_waybel_0(sK6,sK7,sK8)
    | ~ m1_subset_1(sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9))),sK8) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_9076,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,sK8),sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9)))
    | ~ r1_waybel_0(sK6,sK7,sK8)
    | ~ m1_subset_1(sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9))),sK8) ),
    inference(instantiation,[status(thm)],[c_9074])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1102,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | ~ r2_hidden(X0_55,X1_54)
    | ~ r2_hidden(X0_55,X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1214,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,X0_50,sK1(sK6,sK7,X2_54))),X1_54)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,X0_50,sK1(sK6,sK7,X2_54))),X0_54) ),
    inference(instantiation,[status(thm)],[c_1102])).

cnf(c_1776,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X2_54),sK1(sK6,sK7,X3_54))),X1_54)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X2_54),sK1(sK6,sK7,X3_54))),X0_54) ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_2548,plain,
    ( ~ r1_xboole_0(sK8,sK9)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,X1_54))),sK9)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,X1_54))),sK8) ),
    inference(instantiation,[status(thm)],[c_1776])).

cnf(c_8804,plain,
    ( ~ r1_xboole_0(sK8,sK9)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9))),sK9)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9))),sK8) ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_8806,plain,
    ( ~ r1_xboole_0(sK8,sK9)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9))),sK9)
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9))),sK8) ),
    inference(instantiation,[status(thm)],[c_8804])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK4(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7))
    | ~ v7_waybel_0(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_10,c_359])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_20,c_19])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X1,X0),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_455])).

cnf(c_1089,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X1_50,X0_50),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_456])).

cnf(c_1174,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | m1_subset_1(sK4(sK7,X0_50,sK1(sK6,sK7,X0_54)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,X0_54),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_1244,plain,
    ( m1_subset_1(sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,X1_54)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,X0_54),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,X1_54),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_7529,plain,
    ( m1_subset_1(sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,X0_54),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_7531,plain,
    ( m1_subset_1(sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_7529])).

cnf(c_8,plain,
    ( r1_orders_2(X0,X1,sK4(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_432,plain,
    ( r1_orders_2(sK7,X0,sK4(sK7,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v7_waybel_0(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_8,c_359])).

cnf(c_434,plain,
    ( r1_orders_2(sK7,X0,sK4(sK7,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_20,c_19])).

cnf(c_1090,plain,
    ( r1_orders_2(sK7,X0_50,sK4(sK7,X1_50,X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_434])).

cnf(c_1179,plain,
    ( r1_orders_2(sK7,sK1(sK6,sK7,X0_54),sK4(sK7,X0_50,sK1(sK6,sK7,X0_54)))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,X0_54),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_1517,plain,
    ( r1_orders_2(sK7,sK1(sK6,sK7,X0_54),sK4(sK7,sK1(sK6,sK7,X1_54),sK1(sK6,sK7,X0_54)))
    | ~ m1_subset_1(sK1(sK6,sK7,X0_54),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,X1_54),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_5170,plain,
    ( r1_orders_2(sK7,sK1(sK6,sK7,sK9),sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9)))
    | ~ m1_subset_1(sK1(sK6,sK7,X0_54),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_5176,plain,
    ( r1_orders_2(sK7,sK1(sK6,sK7,sK9),sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9)))
    | ~ m1_subset_1(sK1(sK6,sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK1(sK6,sK7,sK8),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_5170])).

cnf(c_3022,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,sK9),sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,X1_54)))
    | ~ r1_waybel_0(sK6,sK7,sK9)
    | ~ m1_subset_1(sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,X1_54)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,X1_54))),sK9) ),
    inference(instantiation,[status(thm)],[c_1295])).

cnf(c_5169,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,sK9),sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9)))
    | ~ r1_waybel_0(sK6,sK7,sK9)
    | ~ m1_subset_1(sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,X0_54),sK1(sK6,sK7,sK9))),sK9) ),
    inference(instantiation,[status(thm)],[c_3022])).

cnf(c_5172,plain,
    ( ~ r1_orders_2(sK7,sK1(sK6,sK7,sK9),sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9)))
    | ~ r1_waybel_0(sK6,sK7,sK9)
    | ~ m1_subset_1(sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9)),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK4(sK7,sK1(sK6,sK7,sK8),sK1(sK6,sK7,sK9))),sK9) ),
    inference(instantiation,[status(thm)],[c_5169])).

cnf(c_17,negated_conjecture,
    ( r1_waybel_0(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_280,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0)
    | m1_subset_1(sK1(sK6,sK7,X0),u1_struct_0(sK7))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_4,c_18])).

cnf(c_284,plain,
    ( m1_subset_1(sK1(sK6,sK7,X0),u1_struct_0(sK7))
    | ~ r1_waybel_0(sK6,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_22,c_21,c_20])).

cnf(c_285,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0)
    | m1_subset_1(sK1(sK6,sK7,X0),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_662,plain,
    ( m1_subset_1(sK1(sK6,sK7,sK8),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_17,c_285])).

cnf(c_16,negated_conjecture,
    ( r1_waybel_0(sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_642,plain,
    ( m1_subset_1(sK1(sK6,sK7,sK9),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_16,c_285])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11123,c_9076,c_8806,c_7531,c_5176,c_5172,c_662,c_642,c_15,c_16,c_17])).


%------------------------------------------------------------------------------
