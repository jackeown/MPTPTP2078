%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:06 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.40s
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

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(nnf_transformation,[],[f14])).

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

fof(f49,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK6(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0))
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
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),X0_51)
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),X0_51)
    | ~ r1_waybel_0(sK7,sK8,X0_54)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1374,plain,
    ( r2_waybel_0(sK7,sK8,X0_54)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,X0_51,sK1(sK7,sK8,X1_54)))
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,X0_51,sK1(sK7,sK8,X1_54)))
    | ~ r1_waybel_0(sK7,sK8,X0_54)
    | ~ m1_subset_1(sK6(sK8,X0_51,sK1(sK7,sK8,X1_54)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_1673,plain,
    ( r2_waybel_0(sK7,sK8,X0_54)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)))
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)))
    | ~ r1_waybel_0(sK7,sK8,X0_54)
    | ~ m1_subset_1(sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1675,plain,
    ( r2_waybel_0(sK7,sK8,sK9)
    | ~ r1_orders_2(sK8,sK2(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
    | ~ r1_orders_2(sK8,sK1(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
    | ~ r1_waybel_0(sK7,sK8,sK9)
    | ~ m1_subset_1(sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_15,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_10,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_612,plain,
    ( l1_orders_2(sK8)
    | ~ l1_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_10,c_19])).

cnf(c_614,plain,
    ( l1_orders_2(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_22])).

cnf(c_912,plain,
    ( r1_orders_2(sK8,X0,sK6(sK8,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_15,c_614])).

cnf(c_20,negated_conjecture,
    ( v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_916,plain,
    ( r1_orders_2(sK8,X0,sK6(sK8,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_912,c_21,c_20])).

cnf(c_1258,plain,
    ( r1_orders_2(sK8,X0_51,sK6(sK8,X0_51,X1_51))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_916])).

cnf(c_1353,plain,
    ( r1_orders_2(sK8,X0_51,sK6(sK8,X0_51,sK1(sK7,sK8,X0_54)))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_1454,plain,
    ( r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X0_54),sK1(sK7,sK8,X1_54)))
    | ~ m1_subset_1(sK2(sK7,sK8,X0_54),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X1_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_1456,plain,
    ( r1_orders_2(sK8,sK2(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_14,plain,
    ( r1_orders_2(X0,X1,sK6(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_932,plain,
    ( r1_orders_2(sK8,X0,sK6(sK8,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_14,c_614])).

cnf(c_934,plain,
    ( r1_orders_2(sK8,X0,sK6(sK8,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_932,c_21,c_20])).

cnf(c_1257,plain,
    ( r1_orders_2(sK8,X0_51,sK6(sK8,X1_51,X0_51))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK8))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_934])).

cnf(c_1348,plain,
    ( r1_orders_2(sK8,X0_51,sK6(sK8,sK2(sK7,sK8,X0_54),X0_51))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK8))
    | ~ m1_subset_1(sK2(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_1441,plain,
    ( r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X0_54)))
    | ~ m1_subset_1(sK2(sK7,sK8,X1_54),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_1443,plain,
    ( r1_orders_2(sK8,sK1(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
    | ~ m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_892,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X1),u1_struct_0(sK8))
    | ~ v7_waybel_0(sK8)
    | v2_struct_0(sK8) ),
    inference(resolution,[status(thm)],[c_16,c_614])).

cnf(c_896,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0,X1),u1_struct_0(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_892,c_21,c_20])).

cnf(c_897,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X1,X0),u1_struct_0(sK8)) ),
    inference(renaming,[status(thm)],[c_896])).

cnf(c_1259,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK8))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X1_51,X0_51),u1_struct_0(sK8)) ),
    inference(subtyping,[status(esa)],[c_897])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK8))
    | m1_subset_1(sK6(sK8,X0_51,sK1(sK7,sK8,X0_54)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_1259])).

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
    inference(minisat,[status(thm)],[c_1675,c_1456,c_1443,c_1428,c_848,c_689,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.29/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.29/1.00  
% 1.29/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.29/1.00  
% 1.29/1.00  ------  iProver source info
% 1.29/1.00  
% 1.29/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.29/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.29/1.00  git: non_committed_changes: false
% 1.29/1.00  git: last_make_outside_of_git: false
% 1.29/1.00  
% 1.29/1.00  ------ 
% 1.29/1.00  
% 1.29/1.00  ------ Input Options
% 1.29/1.00  
% 1.29/1.00  --out_options                           all
% 1.29/1.00  --tptp_safe_out                         true
% 1.29/1.00  --problem_path                          ""
% 1.29/1.00  --include_path                          ""
% 1.29/1.00  --clausifier                            res/vclausify_rel
% 1.29/1.00  --clausifier_options                    --mode clausify
% 1.29/1.00  --stdin                                 false
% 1.29/1.00  --stats_out                             all
% 1.29/1.00  
% 1.29/1.00  ------ General Options
% 1.29/1.00  
% 1.29/1.00  --fof                                   false
% 1.29/1.00  --time_out_real                         305.
% 1.29/1.00  --time_out_virtual                      -1.
% 1.29/1.00  --symbol_type_check                     false
% 1.29/1.00  --clausify_out                          false
% 1.29/1.00  --sig_cnt_out                           false
% 1.29/1.00  --trig_cnt_out                          false
% 1.29/1.00  --trig_cnt_out_tolerance                1.
% 1.29/1.00  --trig_cnt_out_sk_spl                   false
% 1.29/1.00  --abstr_cl_out                          false
% 1.29/1.00  
% 1.29/1.00  ------ Global Options
% 1.29/1.00  
% 1.29/1.00  --schedule                              default
% 1.29/1.00  --add_important_lit                     false
% 1.29/1.00  --prop_solver_per_cl                    1000
% 1.29/1.00  --min_unsat_core                        false
% 1.29/1.00  --soft_assumptions                      false
% 1.29/1.00  --soft_lemma_size                       3
% 1.29/1.00  --prop_impl_unit_size                   0
% 1.29/1.00  --prop_impl_unit                        []
% 1.29/1.00  --share_sel_clauses                     true
% 1.29/1.00  --reset_solvers                         false
% 1.29/1.00  --bc_imp_inh                            [conj_cone]
% 1.29/1.00  --conj_cone_tolerance                   3.
% 1.29/1.00  --extra_neg_conj                        none
% 1.29/1.00  --large_theory_mode                     true
% 1.29/1.00  --prolific_symb_bound                   200
% 1.29/1.00  --lt_threshold                          2000
% 1.29/1.00  --clause_weak_htbl                      true
% 1.29/1.00  --gc_record_bc_elim                     false
% 1.29/1.00  
% 1.29/1.00  ------ Preprocessing Options
% 1.29/1.00  
% 1.29/1.00  --preprocessing_flag                    true
% 1.29/1.00  --time_out_prep_mult                    0.1
% 1.29/1.00  --splitting_mode                        input
% 1.29/1.00  --splitting_grd                         true
% 1.29/1.00  --splitting_cvd                         false
% 1.29/1.00  --splitting_cvd_svl                     false
% 1.29/1.00  --splitting_nvd                         32
% 1.29/1.00  --sub_typing                            true
% 1.29/1.00  --prep_gs_sim                           true
% 1.29/1.00  --prep_unflatten                        true
% 1.29/1.00  --prep_res_sim                          true
% 1.29/1.00  --prep_upred                            true
% 1.29/1.00  --prep_sem_filter                       exhaustive
% 1.29/1.00  --prep_sem_filter_out                   false
% 1.29/1.00  --pred_elim                             true
% 1.29/1.00  --res_sim_input                         true
% 1.29/1.00  --eq_ax_congr_red                       true
% 1.29/1.00  --pure_diseq_elim                       true
% 1.29/1.00  --brand_transform                       false
% 1.29/1.00  --non_eq_to_eq                          false
% 1.29/1.00  --prep_def_merge                        true
% 1.29/1.00  --prep_def_merge_prop_impl              false
% 1.29/1.00  --prep_def_merge_mbd                    true
% 1.29/1.00  --prep_def_merge_tr_red                 false
% 1.29/1.00  --prep_def_merge_tr_cl                  false
% 1.29/1.00  --smt_preprocessing                     true
% 1.29/1.00  --smt_ac_axioms                         fast
% 1.29/1.00  --preprocessed_out                      false
% 1.29/1.00  --preprocessed_stats                    false
% 1.29/1.00  
% 1.29/1.00  ------ Abstraction refinement Options
% 1.29/1.00  
% 1.29/1.00  --abstr_ref                             []
% 1.29/1.00  --abstr_ref_prep                        false
% 1.29/1.00  --abstr_ref_until_sat                   false
% 1.29/1.00  --abstr_ref_sig_restrict                funpre
% 1.29/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.29/1.00  --abstr_ref_under                       []
% 1.29/1.00  
% 1.29/1.00  ------ SAT Options
% 1.29/1.00  
% 1.29/1.00  --sat_mode                              false
% 1.29/1.00  --sat_fm_restart_options                ""
% 1.29/1.00  --sat_gr_def                            false
% 1.29/1.00  --sat_epr_types                         true
% 1.29/1.00  --sat_non_cyclic_types                  false
% 1.29/1.00  --sat_finite_models                     false
% 1.29/1.00  --sat_fm_lemmas                         false
% 1.29/1.00  --sat_fm_prep                           false
% 1.29/1.00  --sat_fm_uc_incr                        true
% 1.29/1.00  --sat_out_model                         small
% 1.29/1.00  --sat_out_clauses                       false
% 1.29/1.00  
% 1.29/1.00  ------ QBF Options
% 1.29/1.00  
% 1.29/1.00  --qbf_mode                              false
% 1.29/1.00  --qbf_elim_univ                         false
% 1.29/1.00  --qbf_dom_inst                          none
% 1.29/1.00  --qbf_dom_pre_inst                      false
% 1.29/1.00  --qbf_sk_in                             false
% 1.29/1.00  --qbf_pred_elim                         true
% 1.29/1.00  --qbf_split                             512
% 1.29/1.00  
% 1.29/1.00  ------ BMC1 Options
% 1.29/1.00  
% 1.29/1.00  --bmc1_incremental                      false
% 1.29/1.00  --bmc1_axioms                           reachable_all
% 1.29/1.00  --bmc1_min_bound                        0
% 1.29/1.00  --bmc1_max_bound                        -1
% 1.29/1.00  --bmc1_max_bound_default                -1
% 1.29/1.00  --bmc1_symbol_reachability              true
% 1.29/1.00  --bmc1_property_lemmas                  false
% 1.29/1.00  --bmc1_k_induction                      false
% 1.29/1.00  --bmc1_non_equiv_states                 false
% 1.29/1.00  --bmc1_deadlock                         false
% 1.29/1.00  --bmc1_ucm                              false
% 1.29/1.00  --bmc1_add_unsat_core                   none
% 1.29/1.00  --bmc1_unsat_core_children              false
% 1.29/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.29/1.00  --bmc1_out_stat                         full
% 1.29/1.00  --bmc1_ground_init                      false
% 1.29/1.00  --bmc1_pre_inst_next_state              false
% 1.29/1.00  --bmc1_pre_inst_state                   false
% 1.29/1.00  --bmc1_pre_inst_reach_state             false
% 1.29/1.00  --bmc1_out_unsat_core                   false
% 1.29/1.00  --bmc1_aig_witness_out                  false
% 1.29/1.00  --bmc1_verbose                          false
% 1.29/1.00  --bmc1_dump_clauses_tptp                false
% 1.29/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.29/1.00  --bmc1_dump_file                        -
% 1.29/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.29/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.29/1.00  --bmc1_ucm_extend_mode                  1
% 1.29/1.00  --bmc1_ucm_init_mode                    2
% 1.29/1.00  --bmc1_ucm_cone_mode                    none
% 1.29/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.29/1.00  --bmc1_ucm_relax_model                  4
% 1.29/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.29/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.29/1.00  --bmc1_ucm_layered_model                none
% 1.29/1.00  --bmc1_ucm_max_lemma_size               10
% 1.29/1.00  
% 1.29/1.00  ------ AIG Options
% 1.29/1.00  
% 1.29/1.00  --aig_mode                              false
% 1.29/1.00  
% 1.29/1.00  ------ Instantiation Options
% 1.29/1.00  
% 1.29/1.00  --instantiation_flag                    true
% 1.29/1.00  --inst_sos_flag                         false
% 1.29/1.00  --inst_sos_phase                        true
% 1.29/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.29/1.00  --inst_lit_sel_side                     num_symb
% 1.29/1.00  --inst_solver_per_active                1400
% 1.29/1.00  --inst_solver_calls_frac                1.
% 1.29/1.00  --inst_passive_queue_type               priority_queues
% 1.29/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.29/1.00  --inst_passive_queues_freq              [25;2]
% 1.29/1.00  --inst_dismatching                      true
% 1.29/1.00  --inst_eager_unprocessed_to_passive     true
% 1.29/1.00  --inst_prop_sim_given                   true
% 1.29/1.00  --inst_prop_sim_new                     false
% 1.29/1.00  --inst_subs_new                         false
% 1.29/1.00  --inst_eq_res_simp                      false
% 1.29/1.00  --inst_subs_given                       false
% 1.29/1.00  --inst_orphan_elimination               true
% 1.29/1.00  --inst_learning_loop_flag               true
% 1.29/1.00  --inst_learning_start                   3000
% 1.29/1.00  --inst_learning_factor                  2
% 1.29/1.00  --inst_start_prop_sim_after_learn       3
% 1.29/1.00  --inst_sel_renew                        solver
% 1.29/1.00  --inst_lit_activity_flag                true
% 1.29/1.00  --inst_restr_to_given                   false
% 1.29/1.00  --inst_activity_threshold               500
% 1.29/1.00  --inst_out_proof                        true
% 1.29/1.00  
% 1.29/1.00  ------ Resolution Options
% 1.29/1.00  
% 1.29/1.00  --resolution_flag                       true
% 1.29/1.00  --res_lit_sel                           adaptive
% 1.29/1.00  --res_lit_sel_side                      none
% 1.29/1.00  --res_ordering                          kbo
% 1.29/1.00  --res_to_prop_solver                    active
% 1.29/1.00  --res_prop_simpl_new                    false
% 1.29/1.00  --res_prop_simpl_given                  true
% 1.29/1.00  --res_passive_queue_type                priority_queues
% 1.29/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/1.00  --res_passive_queues_freq               [15;5]
% 1.40/1.00  --res_forward_subs                      full
% 1.40/1.00  --res_backward_subs                     full
% 1.40/1.00  --res_forward_subs_resolution           true
% 1.40/1.00  --res_backward_subs_resolution          true
% 1.40/1.00  --res_orphan_elimination                true
% 1.40/1.00  --res_time_limit                        2.
% 1.40/1.00  --res_out_proof                         true
% 1.40/1.00  
% 1.40/1.00  ------ Superposition Options
% 1.40/1.00  
% 1.40/1.00  --superposition_flag                    true
% 1.40/1.00  --sup_passive_queue_type                priority_queues
% 1.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.40/1.00  --demod_completeness_check              fast
% 1.40/1.00  --demod_use_ground                      true
% 1.40/1.00  --sup_to_prop_solver                    passive
% 1.40/1.00  --sup_prop_simpl_new                    true
% 1.40/1.00  --sup_prop_simpl_given                  true
% 1.40/1.00  --sup_fun_splitting                     false
% 1.40/1.00  --sup_smt_interval                      50000
% 1.40/1.00  
% 1.40/1.00  ------ Superposition Simplification Setup
% 1.40/1.00  
% 1.40/1.00  --sup_indices_passive                   []
% 1.40/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/1.00  --sup_full_bw                           [BwDemod]
% 1.40/1.00  --sup_immed_triv                        [TrivRules]
% 1.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/1.00  --sup_immed_bw_main                     []
% 1.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.40/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/1.00  
% 1.40/1.00  ------ Combination Options
% 1.40/1.00  
% 1.40/1.00  --comb_res_mult                         3
% 1.40/1.00  --comb_sup_mult                         2
% 1.40/1.00  --comb_inst_mult                        10
% 1.40/1.00  
% 1.40/1.00  ------ Debug Options
% 1.40/1.00  
% 1.40/1.00  --dbg_backtrace                         false
% 1.40/1.00  --dbg_dump_prop_clauses                 false
% 1.40/1.00  --dbg_dump_prop_clauses_file            -
% 1.40/1.00  --dbg_out_stat                          false
% 1.40/1.00  ------ Parsing...
% 1.40/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.40/1.00  
% 1.40/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.40/1.00  
% 1.40/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.40/1.00  ------ Proving...
% 1.40/1.00  ------ Problem Properties 
% 1.40/1.00  
% 1.40/1.00  
% 1.40/1.00  clauses                                 12
% 1.40/1.00  conjectures                             2
% 1.40/1.00  EPR                                     2
% 1.40/1.00  Horn                                    9
% 1.40/1.00  unary                                   2
% 1.40/1.00  binary                                  2
% 1.40/1.00  lits                                    32
% 1.40/1.00  lits eq                                 0
% 1.40/1.00  fd_pure                                 0
% 1.40/1.00  fd_pseudo                               0
% 1.40/1.00  fd_cond                                 0
% 1.40/1.00  fd_pseudo_cond                          0
% 1.40/1.00  AC symbols                              0
% 1.40/1.00  
% 1.40/1.00  ------ Schedule dynamic 5 is on 
% 1.40/1.00  
% 1.40/1.00  ------ no equalities: superposition off 
% 1.40/1.00  
% 1.40/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.40/1.00  
% 1.40/1.00  
% 1.40/1.00  ------ 
% 1.40/1.00  Current options:
% 1.40/1.00  ------ 
% 1.40/1.00  
% 1.40/1.00  ------ Input Options
% 1.40/1.00  
% 1.40/1.00  --out_options                           all
% 1.40/1.00  --tptp_safe_out                         true
% 1.40/1.00  --problem_path                          ""
% 1.40/1.00  --include_path                          ""
% 1.40/1.00  --clausifier                            res/vclausify_rel
% 1.40/1.00  --clausifier_options                    --mode clausify
% 1.40/1.00  --stdin                                 false
% 1.40/1.00  --stats_out                             all
% 1.40/1.00  
% 1.40/1.00  ------ General Options
% 1.40/1.00  
% 1.40/1.00  --fof                                   false
% 1.40/1.00  --time_out_real                         305.
% 1.40/1.00  --time_out_virtual                      -1.
% 1.40/1.00  --symbol_type_check                     false
% 1.40/1.00  --clausify_out                          false
% 1.40/1.00  --sig_cnt_out                           false
% 1.40/1.00  --trig_cnt_out                          false
% 1.40/1.00  --trig_cnt_out_tolerance                1.
% 1.40/1.00  --trig_cnt_out_sk_spl                   false
% 1.40/1.00  --abstr_cl_out                          false
% 1.40/1.00  
% 1.40/1.00  ------ Global Options
% 1.40/1.00  
% 1.40/1.00  --schedule                              default
% 1.40/1.00  --add_important_lit                     false
% 1.40/1.00  --prop_solver_per_cl                    1000
% 1.40/1.00  --min_unsat_core                        false
% 1.40/1.00  --soft_assumptions                      false
% 1.40/1.00  --soft_lemma_size                       3
% 1.40/1.00  --prop_impl_unit_size                   0
% 1.40/1.00  --prop_impl_unit                        []
% 1.40/1.00  --share_sel_clauses                     true
% 1.40/1.00  --reset_solvers                         false
% 1.40/1.00  --bc_imp_inh                            [conj_cone]
% 1.40/1.00  --conj_cone_tolerance                   3.
% 1.40/1.00  --extra_neg_conj                        none
% 1.40/1.00  --large_theory_mode                     true
% 1.40/1.00  --prolific_symb_bound                   200
% 1.40/1.00  --lt_threshold                          2000
% 1.40/1.00  --clause_weak_htbl                      true
% 1.40/1.00  --gc_record_bc_elim                     false
% 1.40/1.00  
% 1.40/1.00  ------ Preprocessing Options
% 1.40/1.00  
% 1.40/1.00  --preprocessing_flag                    true
% 1.40/1.00  --time_out_prep_mult                    0.1
% 1.40/1.00  --splitting_mode                        input
% 1.40/1.00  --splitting_grd                         true
% 1.40/1.00  --splitting_cvd                         false
% 1.40/1.00  --splitting_cvd_svl                     false
% 1.40/1.00  --splitting_nvd                         32
% 1.40/1.00  --sub_typing                            true
% 1.40/1.00  --prep_gs_sim                           true
% 1.40/1.00  --prep_unflatten                        true
% 1.40/1.00  --prep_res_sim                          true
% 1.40/1.00  --prep_upred                            true
% 1.40/1.00  --prep_sem_filter                       exhaustive
% 1.40/1.00  --prep_sem_filter_out                   false
% 1.40/1.00  --pred_elim                             true
% 1.40/1.00  --res_sim_input                         true
% 1.40/1.00  --eq_ax_congr_red                       true
% 1.40/1.00  --pure_diseq_elim                       true
% 1.40/1.00  --brand_transform                       false
% 1.40/1.00  --non_eq_to_eq                          false
% 1.40/1.00  --prep_def_merge                        true
% 1.40/1.00  --prep_def_merge_prop_impl              false
% 1.40/1.00  --prep_def_merge_mbd                    true
% 1.40/1.00  --prep_def_merge_tr_red                 false
% 1.40/1.00  --prep_def_merge_tr_cl                  false
% 1.40/1.00  --smt_preprocessing                     true
% 1.40/1.00  --smt_ac_axioms                         fast
% 1.40/1.00  --preprocessed_out                      false
% 1.40/1.00  --preprocessed_stats                    false
% 1.40/1.00  
% 1.40/1.00  ------ Abstraction refinement Options
% 1.40/1.00  
% 1.40/1.00  --abstr_ref                             []
% 1.40/1.00  --abstr_ref_prep                        false
% 1.40/1.00  --abstr_ref_until_sat                   false
% 1.40/1.00  --abstr_ref_sig_restrict                funpre
% 1.40/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.40/1.00  --abstr_ref_under                       []
% 1.40/1.00  
% 1.40/1.00  ------ SAT Options
% 1.40/1.00  
% 1.40/1.00  --sat_mode                              false
% 1.40/1.00  --sat_fm_restart_options                ""
% 1.40/1.00  --sat_gr_def                            false
% 1.40/1.00  --sat_epr_types                         true
% 1.40/1.00  --sat_non_cyclic_types                  false
% 1.40/1.00  --sat_finite_models                     false
% 1.40/1.00  --sat_fm_lemmas                         false
% 1.40/1.00  --sat_fm_prep                           false
% 1.40/1.00  --sat_fm_uc_incr                        true
% 1.40/1.00  --sat_out_model                         small
% 1.40/1.00  --sat_out_clauses                       false
% 1.40/1.00  
% 1.40/1.00  ------ QBF Options
% 1.40/1.00  
% 1.40/1.00  --qbf_mode                              false
% 1.40/1.00  --qbf_elim_univ                         false
% 1.40/1.00  --qbf_dom_inst                          none
% 1.40/1.00  --qbf_dom_pre_inst                      false
% 1.40/1.00  --qbf_sk_in                             false
% 1.40/1.00  --qbf_pred_elim                         true
% 1.40/1.00  --qbf_split                             512
% 1.40/1.00  
% 1.40/1.00  ------ BMC1 Options
% 1.40/1.00  
% 1.40/1.00  --bmc1_incremental                      false
% 1.40/1.00  --bmc1_axioms                           reachable_all
% 1.40/1.00  --bmc1_min_bound                        0
% 1.40/1.00  --bmc1_max_bound                        -1
% 1.40/1.00  --bmc1_max_bound_default                -1
% 1.40/1.00  --bmc1_symbol_reachability              true
% 1.40/1.00  --bmc1_property_lemmas                  false
% 1.40/1.00  --bmc1_k_induction                      false
% 1.40/1.00  --bmc1_non_equiv_states                 false
% 1.40/1.00  --bmc1_deadlock                         false
% 1.40/1.00  --bmc1_ucm                              false
% 1.40/1.00  --bmc1_add_unsat_core                   none
% 1.40/1.00  --bmc1_unsat_core_children              false
% 1.40/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.40/1.00  --bmc1_out_stat                         full
% 1.40/1.00  --bmc1_ground_init                      false
% 1.40/1.00  --bmc1_pre_inst_next_state              false
% 1.40/1.00  --bmc1_pre_inst_state                   false
% 1.40/1.00  --bmc1_pre_inst_reach_state             false
% 1.40/1.00  --bmc1_out_unsat_core                   false
% 1.40/1.00  --bmc1_aig_witness_out                  false
% 1.40/1.00  --bmc1_verbose                          false
% 1.40/1.00  --bmc1_dump_clauses_tptp                false
% 1.40/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.40/1.00  --bmc1_dump_file                        -
% 1.40/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.40/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.40/1.00  --bmc1_ucm_extend_mode                  1
% 1.40/1.00  --bmc1_ucm_init_mode                    2
% 1.40/1.00  --bmc1_ucm_cone_mode                    none
% 1.40/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.40/1.00  --bmc1_ucm_relax_model                  4
% 1.40/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.40/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.40/1.00  --bmc1_ucm_layered_model                none
% 1.40/1.00  --bmc1_ucm_max_lemma_size               10
% 1.40/1.00  
% 1.40/1.00  ------ AIG Options
% 1.40/1.00  
% 1.40/1.00  --aig_mode                              false
% 1.40/1.00  
% 1.40/1.00  ------ Instantiation Options
% 1.40/1.00  
% 1.40/1.00  --instantiation_flag                    true
% 1.40/1.00  --inst_sos_flag                         false
% 1.40/1.00  --inst_sos_phase                        true
% 1.40/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.40/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.40/1.00  --inst_lit_sel_side                     none
% 1.40/1.00  --inst_solver_per_active                1400
% 1.40/1.00  --inst_solver_calls_frac                1.
% 1.40/1.00  --inst_passive_queue_type               priority_queues
% 1.40/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.40/1.00  --inst_passive_queues_freq              [25;2]
% 1.40/1.00  --inst_dismatching                      true
% 1.40/1.00  --inst_eager_unprocessed_to_passive     true
% 1.40/1.00  --inst_prop_sim_given                   true
% 1.40/1.00  --inst_prop_sim_new                     false
% 1.40/1.00  --inst_subs_new                         false
% 1.40/1.00  --inst_eq_res_simp                      false
% 1.40/1.00  --inst_subs_given                       false
% 1.40/1.00  --inst_orphan_elimination               true
% 1.40/1.00  --inst_learning_loop_flag               true
% 1.40/1.00  --inst_learning_start                   3000
% 1.40/1.00  --inst_learning_factor                  2
% 1.40/1.00  --inst_start_prop_sim_after_learn       3
% 1.40/1.00  --inst_sel_renew                        solver
% 1.40/1.00  --inst_lit_activity_flag                true
% 1.40/1.00  --inst_restr_to_given                   false
% 1.40/1.00  --inst_activity_threshold               500
% 1.40/1.00  --inst_out_proof                        true
% 1.40/1.00  
% 1.40/1.00  ------ Resolution Options
% 1.40/1.00  
% 1.40/1.00  --resolution_flag                       false
% 1.40/1.00  --res_lit_sel                           adaptive
% 1.40/1.00  --res_lit_sel_side                      none
% 1.40/1.00  --res_ordering                          kbo
% 1.40/1.00  --res_to_prop_solver                    active
% 1.40/1.00  --res_prop_simpl_new                    false
% 1.40/1.00  --res_prop_simpl_given                  true
% 1.40/1.00  --res_passive_queue_type                priority_queues
% 1.40/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.40/1.00  --res_passive_queues_freq               [15;5]
% 1.40/1.00  --res_forward_subs                      full
% 1.40/1.00  --res_backward_subs                     full
% 1.40/1.00  --res_forward_subs_resolution           true
% 1.40/1.00  --res_backward_subs_resolution          true
% 1.40/1.00  --res_orphan_elimination                true
% 1.40/1.00  --res_time_limit                        2.
% 1.40/1.00  --res_out_proof                         true
% 1.40/1.00  
% 1.40/1.00  ------ Superposition Options
% 1.40/1.00  
% 1.40/1.00  --superposition_flag                    false
% 1.40/1.00  --sup_passive_queue_type                priority_queues
% 1.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.40/1.00  --demod_completeness_check              fast
% 1.40/1.00  --demod_use_ground                      true
% 1.40/1.00  --sup_to_prop_solver                    passive
% 1.40/1.00  --sup_prop_simpl_new                    true
% 1.40/1.00  --sup_prop_simpl_given                  true
% 1.40/1.00  --sup_fun_splitting                     false
% 1.40/1.00  --sup_smt_interval                      50000
% 1.40/1.00  
% 1.40/1.00  ------ Superposition Simplification Setup
% 1.40/1.00  
% 1.40/1.00  --sup_indices_passive                   []
% 1.40/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/1.00  --sup_full_bw                           [BwDemod]
% 1.40/1.00  --sup_immed_triv                        [TrivRules]
% 1.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/1.00  --sup_immed_bw_main                     []
% 1.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.40/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.40/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.40/1.00  
% 1.40/1.00  ------ Combination Options
% 1.40/1.00  
% 1.40/1.00  --comb_res_mult                         3
% 1.40/1.00  --comb_sup_mult                         2
% 1.40/1.00  --comb_inst_mult                        10
% 1.40/1.00  
% 1.40/1.00  ------ Debug Options
% 1.40/1.00  
% 1.40/1.00  --dbg_backtrace                         false
% 1.40/1.00  --dbg_dump_prop_clauses                 false
% 1.40/1.00  --dbg_dump_prop_clauses_file            -
% 1.40/1.00  --dbg_out_stat                          false
% 1.40/1.00  
% 1.40/1.00  
% 1.40/1.00  
% 1.40/1.00  
% 1.40/1.00  ------ Proving...
% 1.40/1.00  
% 1.40/1.00  
% 1.40/1.00  % SZS status Theorem for theBenchmark.p
% 1.40/1.00  
% 1.40/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.40/1.00  
% 1.40/1.00  fof(f1,axiom,(
% 1.40/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 1.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/1.00  
% 1.40/1.00  fof(f8,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.40/1.00    inference(ennf_transformation,[],[f1])).
% 1.40/1.00  
% 1.40/1.00  fof(f9,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(flattening,[],[f8])).
% 1.40/1.00  
% 1.40/1.00  fof(f17,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(nnf_transformation,[],[f9])).
% 1.40/1.00  
% 1.40/1.00  fof(f18,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(rectify,[],[f17])).
% 1.40/1.00  
% 1.40/1.00  fof(f20,plain,(
% 1.40/1.00    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f19,plain,(
% 1.40/1.00    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))))),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f21,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK0(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK0(X0,X1,X2,X3)) & m1_subset_1(sK0(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 1.40/1.00  
% 1.40/1.00  fof(f38,plain,(
% 1.40/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK1(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/1.00    inference(cnf_transformation,[],[f21])).
% 1.40/1.00  
% 1.40/1.00  fof(f2,axiom,(
% 1.40/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/1.00  
% 1.40/1.00  fof(f10,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.40/1.00    inference(ennf_transformation,[],[f2])).
% 1.40/1.00  
% 1.40/1.00  fof(f11,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(flattening,[],[f10])).
% 1.40/1.00  
% 1.40/1.00  fof(f22,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(nnf_transformation,[],[f11])).
% 1.40/1.00  
% 1.40/1.00  fof(f23,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(rectify,[],[f22])).
% 1.40/1.00  
% 1.40/1.00  fof(f25,plain,(
% 1.40/1.00    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f24,plain,(
% 1.40/1.00    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f26,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f25,f24])).
% 1.40/1.00  
% 1.40/1.00  fof(f46,plain,(
% 1.40/1.00    ( ! [X4,X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | ~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/1.00    inference(cnf_transformation,[],[f26])).
% 1.40/1.00  
% 1.40/1.00  fof(f5,conjecture,(
% 1.40/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 1.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/1.00  
% 1.40/1.00  fof(f6,negated_conjecture,(
% 1.40/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 1.40/1.00    inference(negated_conjecture,[],[f5])).
% 1.40/1.00  
% 1.40/1.00  fof(f7,plain,(
% 1.40/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X2))))),
% 1.40/1.00    inference(pure_predicate_removal,[],[f6])).
% 1.40/1.00  
% 1.40/1.00  fof(f15,plain,(
% 1.40/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.40/1.00    inference(ennf_transformation,[],[f7])).
% 1.40/1.00  
% 1.40/1.00  fof(f16,plain,(
% 1.40/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.40/1.00    inference(flattening,[],[f15])).
% 1.40/1.00  
% 1.40/1.00  fof(f35,plain,(
% 1.40/1.00    ( ! [X0,X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) => (~r2_waybel_0(X0,X1,sK9) & r1_waybel_0(X0,X1,sK9))) )),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f34,plain,(
% 1.40/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_waybel_0(X0,sK8,X2) & r1_waybel_0(X0,sK8,X2)) & l1_waybel_0(sK8,X0) & v7_waybel_0(sK8) & ~v2_struct_0(sK8))) )),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f33,plain,(
% 1.40/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_waybel_0(X0,X1,X2) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_waybel_0(sK7,X1,X2) & r1_waybel_0(sK7,X1,X2)) & l1_waybel_0(X1,sK7) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK7) & ~v2_struct_0(sK7))),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f36,plain,(
% 1.40/1.00    ((~r2_waybel_0(sK7,sK8,sK9) & r1_waybel_0(sK7,sK8,sK9)) & l1_waybel_0(sK8,sK7) & v7_waybel_0(sK8) & ~v2_struct_0(sK8)) & l1_struct_0(sK7) & ~v2_struct_0(sK7)),
% 1.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f16,f35,f34,f33])).
% 1.40/1.00  
% 1.40/1.00  fof(f58,plain,(
% 1.40/1.00    l1_waybel_0(sK8,sK7)),
% 1.40/1.00    inference(cnf_transformation,[],[f36])).
% 1.40/1.00  
% 1.40/1.00  fof(f54,plain,(
% 1.40/1.00    ~v2_struct_0(sK7)),
% 1.40/1.00    inference(cnf_transformation,[],[f36])).
% 1.40/1.00  
% 1.40/1.00  fof(f55,plain,(
% 1.40/1.00    l1_struct_0(sK7)),
% 1.40/1.00    inference(cnf_transformation,[],[f36])).
% 1.40/1.00  
% 1.40/1.00  fof(f56,plain,(
% 1.40/1.00    ~v2_struct_0(sK8)),
% 1.40/1.00    inference(cnf_transformation,[],[f36])).
% 1.40/1.00  
% 1.40/1.00  fof(f4,axiom,(
% 1.40/1.00    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 1.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/1.00  
% 1.40/1.00  fof(f13,plain,(
% 1.40/1.00    ! [X0] : ((v7_waybel_0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.40/1.00    inference(ennf_transformation,[],[f4])).
% 1.40/1.00  
% 1.40/1.00  fof(f14,plain,(
% 1.40/1.00    ! [X0] : ((v7_waybel_0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(flattening,[],[f13])).
% 1.40/1.00  
% 1.40/1.00  fof(f27,plain,(
% 1.40/1.00    ! [X0] : (((v7_waybel_0(X0) | ? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(nnf_transformation,[],[f14])).
% 1.40/1.00  
% 1.40/1.00  fof(f28,plain,(
% 1.40/1.00    ! [X0] : (((v7_waybel_0(X0) | ? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (? [X6] : (r1_orders_2(X0,X5,X6) & r1_orders_2(X0,X4,X6) & m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(rectify,[],[f27])).
% 1.40/1.00  
% 1.40/1.00  fof(f31,plain,(
% 1.40/1.00    ! [X5,X4,X0] : (? [X6] : (r1_orders_2(X0,X5,X6) & r1_orders_2(X0,X4,X6) & m1_subset_1(X6,u1_struct_0(X0))) => (r1_orders_2(X0,X5,sK6(X0,X4,X5)) & r1_orders_2(X0,X4,sK6(X0,X4,X5)) & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0))))),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f30,plain,(
% 1.40/1.00    ( ! [X1] : (! [X0] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_orders_2(X0,sK5(X0),X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))) )),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f29,plain,(
% 1.40/1.00    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,sK4(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.40/1.00    introduced(choice_axiom,[])).
% 1.40/1.00  
% 1.40/1.00  fof(f32,plain,(
% 1.40/1.00    ! [X0] : (((v7_waybel_0(X0) | ((! [X3] : (~r1_orders_2(X0,sK5(X0),X3) | ~r1_orders_2(X0,sK4(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : ((r1_orders_2(X0,X5,sK6(X0,X4,X5)) & r1_orders_2(X0,X4,sK6(X0,X4,X5)) & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.40/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f28,f31,f30,f29])).
% 1.40/1.00  
% 1.40/1.00  fof(f49,plain,(
% 1.40/1.00    ( ! [X4,X0,X5] : (r1_orders_2(X0,X4,sK6(X0,X4,X5)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.40/1.00    inference(cnf_transformation,[],[f32])).
% 1.40/1.00  
% 1.40/1.00  fof(f3,axiom,(
% 1.40/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.40/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.40/1.00  
% 1.40/1.00  fof(f12,plain,(
% 1.40/1.00    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.40/1.00    inference(ennf_transformation,[],[f3])).
% 1.40/1.00  
% 1.40/1.00  fof(f47,plain,(
% 1.40/1.00    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.40/1.00    inference(cnf_transformation,[],[f12])).
% 1.40/1.00  
% 1.40/1.00  fof(f57,plain,(
% 1.40/1.00    v7_waybel_0(sK8)),
% 1.40/1.00    inference(cnf_transformation,[],[f36])).
% 1.40/1.00  
% 1.40/1.00  fof(f50,plain,(
% 1.40/1.00    ( ! [X4,X0,X5] : (r1_orders_2(X0,X5,sK6(X0,X4,X5)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.40/1.00    inference(cnf_transformation,[],[f32])).
% 1.40/1.00  
% 1.40/1.00  fof(f48,plain,(
% 1.40/1.00    ( ! [X4,X0,X5] : (m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.40/1.00    inference(cnf_transformation,[],[f32])).
% 1.40/1.00  
% 1.40/1.00  fof(f60,plain,(
% 1.40/1.00    ~r2_waybel_0(sK7,sK8,sK9)),
% 1.40/1.00    inference(cnf_transformation,[],[f36])).
% 1.40/1.00  
% 1.40/1.00  fof(f45,plain,(
% 1.40/1.00    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/1.00    inference(cnf_transformation,[],[f26])).
% 1.40/1.00  
% 1.40/1.00  fof(f59,plain,(
% 1.40/1.00    r1_waybel_0(sK7,sK8,sK9)),
% 1.40/1.00    inference(cnf_transformation,[],[f36])).
% 1.40/1.00  
% 1.40/1.00  fof(f37,plain,(
% 1.40/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.40/1.00    inference(cnf_transformation,[],[f21])).
% 1.40/1.00  
% 1.40/1.00  cnf(c_3,plain,
% 1.40/1.00      ( ~ r1_orders_2(X0,sK1(X1,X0,X2),X3)
% 1.40/1.00      | ~ r1_waybel_0(X1,X0,X2)
% 1.40/1.00      | ~ l1_waybel_0(X0,X1)
% 1.40/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.40/1.00      | r2_hidden(k2_waybel_0(X1,X0,X3),X2)
% 1.40/1.00      | ~ l1_struct_0(X1)
% 1.40/1.00      | v2_struct_0(X1)
% 1.40/1.00      | v2_struct_0(X0) ),
% 1.40/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_5,plain,
% 1.40/1.00      ( r2_waybel_0(X0,X1,X2)
% 1.40/1.00      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X3)
% 1.40/1.00      | ~ l1_waybel_0(X1,X0)
% 1.40/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.40/1.00      | ~ r2_hidden(k2_waybel_0(X0,X1,X3),X2)
% 1.40/1.00      | ~ l1_struct_0(X0)
% 1.40/1.00      | v2_struct_0(X0)
% 1.40/1.00      | v2_struct_0(X1) ),
% 1.40/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_429,plain,
% 1.40/1.00      ( r2_waybel_0(X0,X1,X2)
% 1.40/1.00      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X3)
% 1.40/1.00      | ~ r1_orders_2(X1,sK1(X0,X1,X2),X3)
% 1.40/1.00      | ~ r1_waybel_0(X0,X1,X2)
% 1.40/1.00      | ~ l1_waybel_0(X1,X0)
% 1.40/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.40/1.00      | ~ l1_struct_0(X0)
% 1.40/1.00      | v2_struct_0(X0)
% 1.40/1.00      | v2_struct_0(X1) ),
% 1.40/1.00      inference(resolution,[status(thm)],[c_3,c_5]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_19,negated_conjecture,
% 1.40/1.00      ( l1_waybel_0(sK8,sK7) ),
% 1.40/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_472,plain,
% 1.40/1.00      ( r2_waybel_0(sK7,sK8,X0)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0),X1)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0),X1)
% 1.40/1.00      | ~ r1_waybel_0(sK7,sK8,X0)
% 1.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.00      | ~ l1_struct_0(sK7)
% 1.40/1.00      | v2_struct_0(sK8)
% 1.40/1.00      | v2_struct_0(sK7) ),
% 1.40/1.00      inference(resolution,[status(thm)],[c_429,c_19]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_23,negated_conjecture,
% 1.40/1.00      ( ~ v2_struct_0(sK7) ),
% 1.40/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_22,negated_conjecture,
% 1.40/1.00      ( l1_struct_0(sK7) ),
% 1.40/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_21,negated_conjecture,
% 1.40/1.00      ( ~ v2_struct_0(sK8) ),
% 1.40/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_476,plain,
% 1.40/1.00      ( ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.00      | ~ r1_waybel_0(sK7,sK8,X0)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0),X1)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0),X1)
% 1.40/1.00      | r2_waybel_0(sK7,sK8,X0) ),
% 1.40/1.00      inference(global_propositional_subsumption,
% 1.40/1.00                [status(thm)],
% 1.40/1.00                [c_472,c_23,c_22,c_21]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_477,plain,
% 1.40/1.00      ( r2_waybel_0(sK7,sK8,X0)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0),X1)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0),X1)
% 1.40/1.00      | ~ r1_waybel_0(sK7,sK8,X0)
% 1.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8)) ),
% 1.40/1.00      inference(renaming,[status(thm)],[c_476]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1266,plain,
% 1.40/1.00      ( r2_waybel_0(sK7,sK8,X0_54)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),X0_51)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),X0_51)
% 1.40/1.00      | ~ r1_waybel_0(sK7,sK8,X0_54)
% 1.40/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK8)) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_477]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1374,plain,
% 1.40/1.00      ( r2_waybel_0(sK7,sK8,X0_54)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,X0_51,sK1(sK7,sK8,X1_54)))
% 1.40/1.00      | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,X0_51,sK1(sK7,sK8,X1_54)))
% 1.40/1.00      | ~ r1_waybel_0(sK7,sK8,X0_54)
% 1.40/1.00      | ~ m1_subset_1(sK6(sK8,X0_51,sK1(sK7,sK8,X1_54)),u1_struct_0(sK8)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1266]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1673,plain,
% 1.40/1.00      ( r2_waybel_0(sK7,sK8,X0_54)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)))
% 1.40/1.00      | ~ r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)))
% 1.40/1.00      | ~ r1_waybel_0(sK7,sK8,X0_54)
% 1.40/1.00      | ~ m1_subset_1(sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X2_54)),u1_struct_0(sK8)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1374]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1675,plain,
% 1.40/1.00      ( r2_waybel_0(sK7,sK8,sK9)
% 1.40/1.00      | ~ r1_orders_2(sK8,sK2(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
% 1.40/1.00      | ~ r1_orders_2(sK8,sK1(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
% 1.40/1.00      | ~ r1_waybel_0(sK7,sK8,sK9)
% 1.40/1.00      | ~ m1_subset_1(sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)),u1_struct_0(sK8)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1673]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_15,plain,
% 1.40/1.00      ( r1_orders_2(X0,X1,sK6(X0,X1,X2))
% 1.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.40/1.00      | ~ v7_waybel_0(X0)
% 1.40/1.00      | ~ l1_orders_2(X0)
% 1.40/1.00      | v2_struct_0(X0) ),
% 1.40/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_10,plain,
% 1.40/1.00      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | ~ l1_struct_0(X1) ),
% 1.40/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_612,plain,
% 1.40/1.00      ( l1_orders_2(sK8) | ~ l1_struct_0(sK7) ),
% 1.40/1.00      inference(resolution,[status(thm)],[c_10,c_19]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_614,plain,
% 1.40/1.00      ( l1_orders_2(sK8) ),
% 1.40/1.00      inference(global_propositional_subsumption,
% 1.40/1.00                [status(thm)],
% 1.40/1.00                [c_612,c_22]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_912,plain,
% 1.40/1.00      ( r1_orders_2(sK8,X0,sK6(sK8,X0,X1))
% 1.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.40/1.00      | ~ v7_waybel_0(sK8)
% 1.40/1.00      | v2_struct_0(sK8) ),
% 1.40/1.00      inference(resolution,[status(thm)],[c_15,c_614]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_20,negated_conjecture,
% 1.40/1.00      ( v7_waybel_0(sK8) ),
% 1.40/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_916,plain,
% 1.40/1.00      ( r1_orders_2(sK8,X0,sK6(sK8,X0,X1))
% 1.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 1.40/1.00      inference(global_propositional_subsumption,
% 1.40/1.00                [status(thm)],
% 1.40/1.00                [c_912,c_21,c_20]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1258,plain,
% 1.40/1.00      ( r1_orders_2(sK8,X0_51,sK6(sK8,X0_51,X1_51))
% 1.40/1.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK8)) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_916]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1353,plain,
% 1.40/1.00      ( r1_orders_2(sK8,X0_51,sK6(sK8,X0_51,sK1(sK7,sK8,X0_54)))
% 1.40/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1258]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1454,plain,
% 1.40/1.00      ( r1_orders_2(sK8,sK2(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X0_54),sK1(sK7,sK8,X1_54)))
% 1.40/1.00      | ~ m1_subset_1(sK2(sK7,sK8,X0_54),u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(sK1(sK7,sK8,X1_54),u1_struct_0(sK8)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1353]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1456,plain,
% 1.40/1.00      ( r1_orders_2(sK8,sK2(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
% 1.40/1.00      | ~ m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1454]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_14,plain,
% 1.40/1.00      ( r1_orders_2(X0,X1,sK6(X0,X2,X1))
% 1.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.40/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.40/1.00      | ~ v7_waybel_0(X0)
% 1.40/1.00      | ~ l1_orders_2(X0)
% 1.40/1.00      | v2_struct_0(X0) ),
% 1.40/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_932,plain,
% 1.40/1.00      ( r1_orders_2(sK8,X0,sK6(sK8,X1,X0))
% 1.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.40/1.00      | ~ v7_waybel_0(sK8)
% 1.40/1.00      | v2_struct_0(sK8) ),
% 1.40/1.00      inference(resolution,[status(thm)],[c_14,c_614]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_934,plain,
% 1.40/1.00      ( r1_orders_2(sK8,X0,sK6(sK8,X1,X0))
% 1.40/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ),
% 1.40/1.00      inference(global_propositional_subsumption,
% 1.40/1.00                [status(thm)],
% 1.40/1.00                [c_932,c_21,c_20]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1257,plain,
% 1.40/1.00      ( r1_orders_2(sK8,X0_51,sK6(sK8,X1_51,X0_51))
% 1.40/1.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK8)) ),
% 1.40/1.00      inference(subtyping,[status(esa)],[c_934]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1348,plain,
% 1.40/1.00      ( r1_orders_2(sK8,X0_51,sK6(sK8,sK2(sK7,sK8,X0_54),X0_51))
% 1.40/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(sK2(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1257]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1441,plain,
% 1.40/1.00      ( r1_orders_2(sK8,sK1(sK7,sK8,X0_54),sK6(sK8,sK2(sK7,sK8,X1_54),sK1(sK7,sK8,X0_54)))
% 1.40/1.00      | ~ m1_subset_1(sK2(sK7,sK8,X1_54),u1_struct_0(sK8))
% 1.40/1.00      | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
% 1.40/1.00      inference(instantiation,[status(thm)],[c_1348]) ).
% 1.40/1.00  
% 1.40/1.00  cnf(c_1443,plain,
% 1.40/1.00      ( r1_orders_2(sK8,sK1(sK7,sK8,sK9),sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)))
% 1.40/1.00      | ~ m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(instantiation,[status(thm)],[c_1441]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_16,plain,
% 1.40/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.40/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.40/1.01      | m1_subset_1(sK6(X1,X2,X0),u1_struct_0(X1))
% 1.40/1.01      | ~ v7_waybel_0(X1)
% 1.40/1.01      | ~ l1_orders_2(X1)
% 1.40/1.01      | v2_struct_0(X1) ),
% 1.40/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_892,plain,
% 1.40/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.01      | m1_subset_1(sK6(sK8,X0,X1),u1_struct_0(sK8))
% 1.40/1.01      | ~ v7_waybel_0(sK8)
% 1.40/1.01      | v2_struct_0(sK8) ),
% 1.40/1.01      inference(resolution,[status(thm)],[c_16,c_614]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_896,plain,
% 1.40/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.01      | m1_subset_1(sK6(sK8,X0,X1),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(global_propositional_subsumption,
% 1.40/1.01                [status(thm)],
% 1.40/1.01                [c_892,c_21,c_20]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_897,plain,
% 1.40/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 1.40/1.01      | m1_subset_1(sK6(sK8,X1,X0),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(renaming,[status(thm)],[c_896]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_1259,plain,
% 1.40/1.01      ( ~ m1_subset_1(X0_51,u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(X1_51,u1_struct_0(sK8))
% 1.40/1.01      | m1_subset_1(sK6(sK8,X1_51,X0_51),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(subtyping,[status(esa)],[c_897]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_1333,plain,
% 1.40/1.01      ( ~ m1_subset_1(X0_51,u1_struct_0(sK8))
% 1.40/1.01      | m1_subset_1(sK6(sK8,X0_51,sK1(sK7,sK8,X0_54)),u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(sK1(sK7,sK8,X0_54),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(instantiation,[status(thm)],[c_1259]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_1426,plain,
% 1.40/1.01      ( m1_subset_1(sK6(sK8,sK2(sK7,sK8,X0_54),sK1(sK7,sK8,X1_54)),u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(sK2(sK7,sK8,X0_54),u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(sK1(sK7,sK8,X1_54),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(instantiation,[status(thm)],[c_1333]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_1428,plain,
% 1.40/1.01      ( m1_subset_1(sK6(sK8,sK2(sK7,sK8,sK9),sK1(sK7,sK8,sK9)),u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8))
% 1.40/1.01      | ~ m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(instantiation,[status(thm)],[c_1426]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_17,negated_conjecture,
% 1.40/1.01      ( ~ r2_waybel_0(sK7,sK8,sK9) ),
% 1.40/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_6,plain,
% 1.40/1.01      ( r2_waybel_0(X0,X1,X2)
% 1.40/1.01      | ~ l1_waybel_0(X1,X0)
% 1.40/1.01      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 1.40/1.01      | ~ l1_struct_0(X0)
% 1.40/1.01      | v2_struct_0(X0)
% 1.40/1.01      | v2_struct_0(X1) ),
% 1.40/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_538,plain,
% 1.40/1.01      ( r2_waybel_0(sK7,sK8,X0)
% 1.40/1.01      | m1_subset_1(sK2(sK7,sK8,X0),u1_struct_0(sK8))
% 1.40/1.01      | ~ l1_struct_0(sK7)
% 1.40/1.01      | v2_struct_0(sK8)
% 1.40/1.01      | v2_struct_0(sK7) ),
% 1.40/1.01      inference(resolution,[status(thm)],[c_6,c_19]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_542,plain,
% 1.40/1.01      ( m1_subset_1(sK2(sK7,sK8,X0),u1_struct_0(sK8))
% 1.40/1.01      | r2_waybel_0(sK7,sK8,X0) ),
% 1.40/1.01      inference(global_propositional_subsumption,
% 1.40/1.01                [status(thm)],
% 1.40/1.01                [c_538,c_23,c_22,c_21]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_543,plain,
% 1.40/1.01      ( r2_waybel_0(sK7,sK8,X0)
% 1.40/1.01      | m1_subset_1(sK2(sK7,sK8,X0),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(renaming,[status(thm)],[c_542]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_848,plain,
% 1.40/1.01      ( m1_subset_1(sK2(sK7,sK8,sK9),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(resolution,[status(thm)],[c_17,c_543]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_18,negated_conjecture,
% 1.40/1.01      ( r1_waybel_0(sK7,sK8,sK9) ),
% 1.40/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_4,plain,
% 1.40/1.01      ( ~ r1_waybel_0(X0,X1,X2)
% 1.40/1.01      | ~ l1_waybel_0(X1,X0)
% 1.40/1.01      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))
% 1.40/1.01      | ~ l1_struct_0(X0)
% 1.40/1.01      | v2_struct_0(X0)
% 1.40/1.01      | v2_struct_0(X1) ),
% 1.40/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_555,plain,
% 1.40/1.01      ( ~ r1_waybel_0(sK7,sK8,X0)
% 1.40/1.01      | m1_subset_1(sK1(sK7,sK8,X0),u1_struct_0(sK8))
% 1.40/1.01      | ~ l1_struct_0(sK7)
% 1.40/1.01      | v2_struct_0(sK8)
% 1.40/1.01      | v2_struct_0(sK7) ),
% 1.40/1.01      inference(resolution,[status(thm)],[c_4,c_19]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_559,plain,
% 1.40/1.01      ( m1_subset_1(sK1(sK7,sK8,X0),u1_struct_0(sK8))
% 1.40/1.01      | ~ r1_waybel_0(sK7,sK8,X0) ),
% 1.40/1.01      inference(global_propositional_subsumption,
% 1.40/1.01                [status(thm)],
% 1.40/1.01                [c_555,c_23,c_22,c_21]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_560,plain,
% 1.40/1.01      ( ~ r1_waybel_0(sK7,sK8,X0)
% 1.40/1.01      | m1_subset_1(sK1(sK7,sK8,X0),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(renaming,[status(thm)],[c_559]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(c_689,plain,
% 1.40/1.01      ( m1_subset_1(sK1(sK7,sK8,sK9),u1_struct_0(sK8)) ),
% 1.40/1.01      inference(resolution,[status(thm)],[c_18,c_560]) ).
% 1.40/1.01  
% 1.40/1.01  cnf(contradiction,plain,
% 1.40/1.01      ( $false ),
% 1.40/1.01      inference(minisat,
% 1.40/1.01                [status(thm)],
% 1.40/1.01                [c_1675,c_1456,c_1443,c_1428,c_848,c_689,c_17,c_18]) ).
% 1.40/1.01  
% 1.40/1.01  
% 1.40/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.40/1.01  
% 1.40/1.01  ------                               Statistics
% 1.40/1.01  
% 1.40/1.01  ------ General
% 1.40/1.01  
% 1.40/1.01  abstr_ref_over_cycles:                  0
% 1.40/1.01  abstr_ref_under_cycles:                 0
% 1.40/1.01  gc_basic_clause_elim:                   0
% 1.40/1.01  forced_gc_time:                         0
% 1.40/1.01  parsing_time:                           0.01
% 1.40/1.01  unif_index_cands_time:                  0.
% 1.40/1.01  unif_index_add_time:                    0.
% 1.40/1.01  orderings_time:                         0.
% 1.40/1.01  out_proof_time:                         0.011
% 1.40/1.01  total_time:                             0.083
% 1.40/1.01  num_of_symbols:                         55
% 1.40/1.01  num_of_terms:                           1688
% 1.40/1.01  
% 1.40/1.01  ------ Preprocessing
% 1.40/1.01  
% 1.40/1.01  num_of_splits:                          0
% 1.40/1.01  num_of_split_atoms:                     0
% 1.40/1.01  num_of_reused_defs:                     0
% 1.40/1.01  num_eq_ax_congr_red:                    0
% 1.40/1.01  num_of_sem_filtered_clauses:            0
% 1.40/1.01  num_of_subtypes:                        5
% 1.40/1.01  monotx_restored_types:                  0
% 1.40/1.01  sat_num_of_epr_types:                   0
% 1.40/1.01  sat_num_of_non_cyclic_types:            0
% 1.40/1.01  sat_guarded_non_collapsed_types:        0
% 1.40/1.01  num_pure_diseq_elim:                    0
% 1.40/1.01  simp_replaced_by:                       0
% 1.40/1.01  res_preprocessed:                       36
% 1.40/1.01  prep_upred:                             0
% 1.40/1.01  prep_unflattend:                        0
% 1.40/1.01  smt_new_axioms:                         0
% 1.40/1.01  pred_elim_cands:                        4
% 1.40/1.01  pred_elim:                              6
% 1.40/1.01  pred_elim_cl:                           12
% 1.40/1.01  pred_elim_cycles:                       12
% 1.40/1.01  merged_defs:                            0
% 1.40/1.01  merged_defs_ncl:                        0
% 1.40/1.01  bin_hyper_res:                          0
% 1.40/1.01  prep_cycles:                            2
% 1.40/1.01  pred_elim_time:                         0.019
% 1.40/1.01  splitting_time:                         0.
% 1.40/1.01  sem_filter_time:                        0.
% 1.40/1.01  monotx_time:                            0.
% 1.40/1.01  subtype_inf_time:                       0.
% 1.40/1.01  
% 1.40/1.01  ------ Problem properties
% 1.40/1.01  
% 1.40/1.01  clauses:                                12
% 1.40/1.01  conjectures:                            2
% 1.40/1.01  epr:                                    2
% 1.40/1.01  horn:                                   9
% 1.40/1.01  ground:                                 2
% 1.40/1.01  unary:                                  2
% 1.40/1.01  binary:                                 2
% 1.40/1.01  lits:                                   32
% 1.40/1.01  lits_eq:                                0
% 1.40/1.01  fd_pure:                                0
% 1.40/1.01  fd_pseudo:                              0
% 1.40/1.01  fd_cond:                                0
% 1.40/1.01  fd_pseudo_cond:                         0
% 1.40/1.01  ac_symbols:                             0
% 1.40/1.01  
% 1.40/1.01  ------ Propositional Solver
% 1.40/1.01  
% 1.40/1.01  prop_solver_calls:                      14
% 1.40/1.01  prop_fast_solver_calls:                 529
% 1.40/1.01  smt_solver_calls:                       0
% 1.40/1.01  smt_fast_solver_calls:                  0
% 1.40/1.01  prop_num_of_clauses:                    513
% 1.40/1.01  prop_preprocess_simplified:             1674
% 1.40/1.01  prop_fo_subsumed:                       32
% 1.40/1.01  prop_solver_time:                       0.
% 1.40/1.01  smt_solver_time:                        0.
% 1.40/1.01  smt_fast_solver_time:                   0.
% 1.40/1.01  prop_fast_solver_time:                  0.
% 1.40/1.01  prop_unsat_core_time:                   0.
% 1.40/1.01  
% 1.40/1.01  ------ QBF
% 1.40/1.01  
% 1.40/1.01  qbf_q_res:                              0
% 1.40/1.01  qbf_num_tautologies:                    0
% 1.40/1.01  qbf_prep_cycles:                        0
% 1.40/1.01  
% 1.40/1.01  ------ BMC1
% 1.40/1.01  
% 1.40/1.01  bmc1_current_bound:                     -1
% 1.40/1.01  bmc1_last_solved_bound:                 -1
% 1.40/1.01  bmc1_unsat_core_size:                   -1
% 1.40/1.01  bmc1_unsat_core_parents_size:           -1
% 1.40/1.01  bmc1_merge_next_fun:                    0
% 1.40/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.40/1.01  
% 1.40/1.01  ------ Instantiation
% 1.40/1.01  
% 1.40/1.01  inst_num_of_clauses:                    77
% 1.40/1.01  inst_num_in_passive:                    35
% 1.40/1.01  inst_num_in_active:                     29
% 1.40/1.01  inst_num_in_unprocessed:                12
% 1.40/1.01  inst_num_of_loops:                      34
% 1.40/1.01  inst_num_of_learning_restarts:          0
% 1.40/1.01  inst_num_moves_active_passive:          2
% 1.40/1.01  inst_lit_activity:                      0
% 1.40/1.01  inst_lit_activity_moves:                0
% 1.40/1.01  inst_num_tautologies:                   0
% 1.40/1.01  inst_num_prop_implied:                  0
% 1.40/1.01  inst_num_existing_simplified:           0
% 1.40/1.01  inst_num_eq_res_simplified:             0
% 1.40/1.01  inst_num_child_elim:                    0
% 1.40/1.01  inst_num_of_dismatching_blockings:      8
% 1.40/1.01  inst_num_of_non_proper_insts:           42
% 1.40/1.01  inst_num_of_duplicates:                 0
% 1.40/1.01  inst_inst_num_from_inst_to_res:         0
% 1.40/1.01  inst_dismatching_checking_time:         0.
% 1.40/1.01  
% 1.40/1.01  ------ Resolution
% 1.40/1.01  
% 1.40/1.01  res_num_of_clauses:                     0
% 1.40/1.01  res_num_in_passive:                     0
% 1.40/1.01  res_num_in_active:                      0
% 1.40/1.01  res_num_of_loops:                       38
% 1.40/1.01  res_forward_subset_subsumed:            3
% 1.40/1.01  res_backward_subset_subsumed:           0
% 1.40/1.01  res_forward_subsumed:                   0
% 1.40/1.01  res_backward_subsumed:                  0
% 1.40/1.01  res_forward_subsumption_resolution:     0
% 1.40/1.01  res_backward_subsumption_resolution:    0
% 1.40/1.01  res_clause_to_clause_subsumption:       15
% 1.40/1.01  res_orphan_elimination:                 0
% 1.40/1.01  res_tautology_del:                      2
% 1.40/1.01  res_num_eq_res_simplified:              0
% 1.40/1.01  res_num_sel_changes:                    0
% 1.40/1.01  res_moves_from_active_to_pass:          0
% 1.40/1.01  
% 1.40/1.01  ------ Superposition
% 1.40/1.01  
% 1.40/1.01  sup_time_total:                         0.
% 1.40/1.01  sup_time_generating:                    0.
% 1.40/1.01  sup_time_sim_full:                      0.
% 1.40/1.01  sup_time_sim_immed:                     0.
% 1.40/1.01  
% 1.40/1.01  sup_num_of_clauses:                     0
% 1.40/1.01  sup_num_in_active:                      0
% 1.40/1.01  sup_num_in_passive:                     0
% 1.40/1.01  sup_num_of_loops:                       0
% 1.40/1.01  sup_fw_superposition:                   0
% 1.40/1.01  sup_bw_superposition:                   0
% 1.40/1.01  sup_immediate_simplified:               0
% 1.40/1.01  sup_given_eliminated:                   0
% 1.40/1.01  comparisons_done:                       0
% 1.40/1.01  comparisons_avoided:                    0
% 1.40/1.01  
% 1.40/1.01  ------ Simplifications
% 1.40/1.01  
% 1.40/1.01  
% 1.40/1.01  sim_fw_subset_subsumed:                 0
% 1.40/1.01  sim_bw_subset_subsumed:                 0
% 1.40/1.01  sim_fw_subsumed:                        0
% 1.40/1.01  sim_bw_subsumed:                        0
% 1.40/1.01  sim_fw_subsumption_res:                 0
% 1.40/1.01  sim_bw_subsumption_res:                 0
% 1.40/1.01  sim_tautology_del:                      0
% 1.40/1.01  sim_eq_tautology_del:                   0
% 1.40/1.01  sim_eq_res_simp:                        0
% 1.40/1.01  sim_fw_demodulated:                     0
% 1.40/1.01  sim_bw_demodulated:                     0
% 1.40/1.01  sim_light_normalised:                   0
% 1.40/1.01  sim_joinable_taut:                      0
% 1.40/1.01  sim_joinable_simp:                      0
% 1.40/1.01  sim_ac_normalised:                      0
% 1.40/1.01  sim_smt_subsumption:                    0
% 1.40/1.01  
%------------------------------------------------------------------------------
