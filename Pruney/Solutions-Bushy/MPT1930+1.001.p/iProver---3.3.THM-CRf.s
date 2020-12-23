%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1930+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:53 EST 2020

% Result     : Theorem 0.89s
% Output     : CNFRefutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 435 expanded)
%              Number of clauses        :   53 (  80 expanded)
%              Number of leaves         :   15 ( 139 expanded)
%              Depth                    :   17
%              Number of atoms          :  580 (2942 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f38,plain,(
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

fof(f2,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f25,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f25,f24])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,conjecture,(
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

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( r1_waybel_0(X0,X1,X2)
               => r2_waybel_0(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_waybel_0(X0,X1,X2)
          & r1_waybel_0(X0,X1,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK9)
        & r1_waybel_0(X0,X1,sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(X0,X1,X2)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_waybel_0(X0,sK8,X2)
            & r1_waybel_0(X0,sK8,X2) )
        & l1_waybel_0(sK8,X0)
        & v7_waybel_0(sK8)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_waybel_0(X0,X1,X2)
                & r1_waybel_0(X0,X1,X2) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_waybel_0(sK7,X1,X2)
              & r1_waybel_0(sK7,X1,X2) )
          & l1_waybel_0(X1,sK7)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r2_waybel_0(sK7,sK8,sK9)
    & r1_waybel_0(sK7,sK8,sK9)
    & l1_waybel_0(sK8,sK7)
    & v7_waybel_0(sK8)
    & ~ v2_struct_0(sK8)
    & l1_struct_0(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f16,f35,f34,f33])).

fof(f58,plain,(
    l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X4,X0] :
      ( ? [X6] :
          ( r1_orders_2(X0,X5,X6)
          & r1_orders_2(X0,X4,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
        & r1_orders_2(X0,X4,sK6(X0,X4,X5))
        & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_orders_2(X0,sK5(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
                | ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ( ! [X3] :
                ( ~ r1_orders_2(X0,sK5(X0),X3)
                | ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
                    & r1_orders_2(X0,X4,sK6(X0,X4,X5))
                    & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f28,f31,f30,f29])).

fof(f48,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK6(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ~ r2_waybel_0(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    r1_waybel_0(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,sK1(X1,X0,X2),X3)
    | ~ r1_waybel_0(X1,X0,X2)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(k2_waybel_0(X1,X0,X3),X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_orders_2(X1,sK2(X0,X1,X2),X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_waybel_0(X0,X1,X3),X2)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_429,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ r1_orders_2(X1,sK2(X0,X1,X2),X3)
    | ~ r1_orders_2(X1,sK1(X0,X1,X2),X3)
    | ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_3,c_5])).

cnf(c_19,negated_conjecture,
    ( l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_472,plain,
    ( r2_waybel_0(sK7,sK8,X0)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0),X1)
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0),X1)
    | ~ r1_waybel_0(sK7,sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ l1_struct_0(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_429,c_19])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r1_waybel_0(sK7,sK8,X0)
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0),X1)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0),X1)
    | r2_waybel_0(sK7,sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_23,c_22,c_21])).

cnf(c_477,plain,
    ( r2_waybel_0(sK7,sK8,X0)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0),X1)
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0),X1)
    | ~ r1_waybel_0(sK7,sK8,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_1266,plain,
    ( r2_waybel_0(sK7,sK8,X0_54)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),X0_50)
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),X0_50)
    | ~ r1_waybel_0(sK7,sK8,X0_54)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1366,plain,
    ( r2_waybel_0(sK7,sK8,X0_54)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,X0_50,sK1(sK7,sK8,X1_54)))
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,X0_50,sK1(sK7,sK8,X1_54)))
    | ~ r1_waybel_0(sK7,sK8,X0_54)
    | ~ m1_subset_1(sK6(sK8,X0_50,sK1(sK7,sK8,X1_54)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_1673,plain,
    ( r2_waybel_0(sK7,sK8,X0_54)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)))
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)))
    | ~ r1_waybel_0(sK7,sK8,X0_54)
    | ~ m1_subset_1(sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_1675,plain,
    ( r2_waybel_0(sK7,sK8,sK9)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
    | ~ r1_waybel_0(sK7,sK8,sK9)
    | ~ m1_subset_1(sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_14,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_612,plain,
    ( l1_orders_2(sK8)
    | ~ l1_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_16,c_19])).

cnf(c_614,plain,
    ( l1_orders_2(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_22])).

cnf(c_892,plain,
    ( r1_orders_2(sK8,X0,sK6(sK8,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_14,c_614])).

cnf(c_20,negated_conjecture,
    ( v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_896,plain,
    ( r1_orders_2(sK8,X0,sK6(sK8,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_892,c_21,c_20])).

cnf(c_1259,plain,
    ( r1_orders_2(sK8,X0_50,sK6(sK8,X0_50,X1_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_896])).

cnf(c_1358,plain,
    ( r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X0_54),X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK8))
    | ~ m1_subset_1(sK2(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_1459,plain,
    ( r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X0_54),sK1(sK7,sK8,X1_54)))
    | ~ m1_subset_1(sK2(sK7,sK8,X0_54),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X1_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1358])).

cnf(c_1461,plain,
    ( r1_orders_2(sK8,sK2(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_931,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X1),u1_struct_0(sK8))
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_15,c_614])).

cnf(c_935,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_931,c_21,c_20])).

cnf(c_936,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_935])).

cnf(c_1257,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X1_50,X0_50),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_936])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(X0_50,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0_50,sK1(sK7,sK8,X0_54)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_1426,plain,
    ( m1_subset_1(sK6(sK8,sK2(sK7,sK8,X0_54),sK1(sK7,sK8,X1_54)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK2(sK7,sK8,X0_54),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X1_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_1428,plain,
    ( m1_subset_1(sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_912,plain,
    ( r1_orders_2(sK8,X0,sK6(sK8,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_13,c_614])).

cnf(c_914,plain,
    ( r1_orders_2(sK8,X0,sK6(sK8,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_912,c_21,c_20])).

cnf(c_1258,plain,
    ( r1_orders_2(sK8,X0_50,sK6(sK8,X1_50,X0_50))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_914])).

cnf(c_1343,plain,
    ( r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,X0_50,sK1(sK7,sK8,X0_54)))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_1416,plain,
    ( r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X0_54)))
    | ~ m1_subset_1(sK2(sK7,sK8,X1_54),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_1418,plain,
    ( r1_orders_2(sK8,sK1(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_17,negated_conjecture,
    ( ~ r2_waybel_0(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_6,plain,
    ( r2_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_538,plain,
    ( r2_waybel_0(sK7,sK8,X0)
    | m1_subset_1(sK2(sK7,sK8,X0),u1_struct_0(sK8))
    | ~ l1_struct_0(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_6,c_19])).

cnf(c_542,plain,
    ( m1_subset_1(sK2(sK7,sK8,X0),u1_struct_0(sK8))
    | r2_waybel_0(sK7,sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_23,c_22,c_21])).

cnf(c_543,plain,
    ( r2_waybel_0(sK7,sK8,X0)
    | m1_subset_1(sK2(sK7,sK8,X0),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_542])).

cnf(c_848,plain,
    ( m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_17,c_543])).

cnf(c_18,negated_conjecture,
    ( r1_waybel_0(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_555,plain,
    ( ~ r1_waybel_0(sK7,sK8,X0)
    | m1_subset_1(sK1(sK7,sK8,X0),u1_struct_0(sK8))
    | ~ l1_struct_0(sK7)
    | v2_struct_0(sK8)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_4,c_19])).

cnf(c_559,plain,
    ( m1_subset_1(sK1(sK7,sK8,X0),u1_struct_0(sK8))
    | ~ r1_waybel_0(sK7,sK8,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_23,c_22,c_21])).

cnf(c_560,plain,
    ( ~ r1_waybel_0(sK7,sK8,X0)
    | m1_subset_1(sK1(sK7,sK8,X0),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_689,plain,
    ( m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
    inference(resolution,[status(thm)],[c_18,c_560])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1675,c_1461,c_1428,c_1418,c_848,c_689,c_17,c_18])).


%------------------------------------------------------------------------------
