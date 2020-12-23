%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:06 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 683 expanded)
%              Number of clauses        :   52 ( 121 expanded)
%              Number of leaves         :   14 ( 220 expanded)
%              Depth                    :   20
%              Number of atoms          :  499 (5125 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X5,X4,X0] :
      ( ? [X6] :
          ( r1_orders_2(X0,X5,X6)
          & r1_orders_2(X0,X4,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X5,sK5(X0,X4,X5))
        & r1_orders_2(X0,X4,sK5(X0,X4,X5))
        & m1_subset_1(sK5(X0,X4,X5),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_orders_2(X0,sK4(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ( ! [X3] :
                ( ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ r1_orders_2(X0,sK3(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ( r1_orders_2(X0,X5,sK5(X0,X4,X5))
                    & r1_orders_2(X0,X4,sK5(X0,X4,X5))
                    & m1_subset_1(sK5(X0,X4,X5),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f28,f27,f26])).

fof(f43,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK5(X0,X4,X5),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f45,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK5(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
                      & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f22,f21])).

fof(f38,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK5(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
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
    inference(rectify,[],[f1])).

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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f17])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    r1_xboole_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    r1_waybel_0(sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    r1_waybel_0(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ v7_waybel_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,negated_conjecture,
    ( l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_357,plain,
    ( l1_orders_2(sK7)
    | ~ l1_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_8,c_18])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_359,plain,
    ( l1_orders_2(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_21])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0,X1),u1_struct_0(sK7))
    | ~ v7_waybel_0(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_14,c_359])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X0,X1),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_412,c_20,c_19])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X1,X0),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_416])).

cnf(c_1091,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
    | m1_subset_1(sK5(sK7,X1_51,X0_51),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_12,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_452,plain,
    ( r1_orders_2(sK7,X0,sK5(sK7,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v7_waybel_0(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_12,c_359])).

cnf(c_454,plain,
    ( r1_orders_2(sK7,X0,sK5(sK7,X1,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_20,c_19])).

cnf(c_1089,plain,
    ( r1_orders_2(sK7,X0_51,sK5(sK7,X1_51,X0_51))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,sK2(X1,X0,X2),X3)
    | ~ r1_waybel_0(X1,X0,X2)
    | ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(k2_waybel_0(X1,X0,X3),X2)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_367,plain,
    ( ~ r1_orders_2(sK7,sK2(sK6,sK7,X0),X1)
    | ~ r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,X1),X0)
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_6,c_18])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_371,plain,
    ( r2_hidden(k2_waybel_0(sK6,sK7,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r1_waybel_0(sK6,sK7,X0)
    | ~ r1_orders_2(sK7,sK2(sK6,sK7,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_22,c_21,c_20])).

cnf(c_372,plain,
    ( ~ r1_orders_2(sK7,sK2(sK6,sK7,X0),X1)
    | ~ r1_waybel_0(sK6,sK7,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,X1),X0) ),
    inference(renaming,[status(thm)],[c_371])).

cnf(c_1092,plain,
    ( ~ r1_orders_2(sK7,sK2(sK6,sK7,X0_54),X0_51)
    | ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,X0_51),X0_54) ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_1408,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,X0_51,sK2(sK6,sK7,X0_54)),u1_struct_0(sK7))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,X0_51,sK2(sK6,sK7,X0_54))),X0_54) ),
    inference(resolution,[status(thm)],[c_1089,c_1092])).

cnf(c_1529,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,X0_51,sK2(sK6,sK7,X0_54))),X0_54) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1091,c_1408])).

cnf(c_7,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_280,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0)
    | m1_subset_1(sK2(sK6,sK7,X0),u1_struct_0(sK7))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6) ),
    inference(resolution,[status(thm)],[c_7,c_18])).

cnf(c_284,plain,
    ( m1_subset_1(sK2(sK6,sK7,X0),u1_struct_0(sK7))
    | ~ r1_waybel_0(sK6,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_22,c_21,c_20])).

cnf(c_285,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0)
    | m1_subset_1(sK2(sK6,sK7,X0),u1_struct_0(sK7)) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_1096,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0_54)
    | m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_285])).

cnf(c_3249,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ r1_waybel_0(sK6,sK7,X0_54)
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,X0_51,sK2(sK6,sK7,X0_54))),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1529,c_1096])).

cnf(c_3250,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,X0_51,sK2(sK6,sK7,X0_54))),X0_54) ),
    inference(renaming,[status(thm)],[c_3249])).

cnf(c_13,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_432,plain,
    ( r1_orders_2(sK7,X0,sK5(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ v7_waybel_0(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[status(thm)],[c_13,c_359])).

cnf(c_436,plain,
    ( r1_orders_2(sK7,X0,sK5(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_20,c_19])).

cnf(c_1090,plain,
    ( r1_orders_2(sK7,X0_51,sK5(sK7,X0_51,X1_51))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_436])).

cnf(c_1517,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(sK5(sK7,sK2(sK6,sK7,X0_54),X0_51),u1_struct_0(sK7))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,X0_54),X0_51)),X0_54) ),
    inference(resolution,[status(thm)],[c_1090,c_1092])).

cnf(c_1528,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,X0_54),X0_51)),X0_54) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1091,c_1517])).

cnf(c_2360,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ r1_waybel_0(sK6,sK7,X0_54)
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,X0_54),X0_51)),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1528,c_1096])).

cnf(c_2361,plain,
    ( ~ r1_waybel_0(sK6,sK7,X0_54)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,X0_54),X0_51)),X0_54) ),
    inference(renaming,[status(thm)],[c_2360])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1102,plain,
    ( ~ r2_hidden(X0_55,X0_54)
    | ~ r2_hidden(X0_55,X1_54)
    | ~ r1_xboole_0(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1099,negated_conjecture,
    ( r1_xboole_0(sK8,sK9) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1840,plain,
    ( ~ r2_hidden(X0_55,sK9)
    | ~ r2_hidden(X0_55,sK8) ),
    inference(resolution,[status(thm)],[c_1102,c_1099])).

cnf(c_2619,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK9)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,sK9),X0_51)),sK8) ),
    inference(resolution,[status(thm)],[c_2361,c_1840])).

cnf(c_16,negated_conjecture,
    ( r1_waybel_0(sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2624,plain,
    ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
    | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,sK9),X0_51)),sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2619,c_16])).

cnf(c_3275,plain,
    ( ~ r1_waybel_0(sK6,sK7,sK8)
    | ~ m1_subset_1(sK2(sK6,sK7,sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_3250,c_2624])).

cnf(c_17,negated_conjecture,
    ( r1_waybel_0(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_662,plain,
    ( m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_17,c_285])).

cnf(c_642,plain,
    ( m1_subset_1(sK2(sK6,sK7,sK9),u1_struct_0(sK7)) ),
    inference(resolution,[status(thm)],[c_16,c_285])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3275,c_662,c_642,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:55:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.52/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.99  
% 2.52/0.99  ------  iProver source info
% 2.52/0.99  
% 2.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.99  git: non_committed_changes: false
% 2.52/0.99  git: last_make_outside_of_git: false
% 2.52/0.99  
% 2.52/0.99  ------ 
% 2.52/0.99  ------ Parsing...
% 2.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.99  ------ Proving...
% 2.52/0.99  ------ Problem Properties 
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  clauses                                 14
% 2.52/0.99  conjectures                             3
% 2.52/0.99  EPR                                     4
% 2.52/0.99  Horn                                    10
% 2.52/0.99  unary                                   3
% 2.52/0.99  binary                                  3
% 2.52/0.99  lits                                    34
% 2.52/0.99  lits eq                                 0
% 2.52/0.99  fd_pure                                 0
% 2.52/0.99  fd_pseudo                               0
% 2.52/0.99  fd_cond                                 0
% 2.52/0.99  fd_pseudo_cond                          0
% 2.52/0.99  AC symbols                              0
% 2.52/0.99  
% 2.52/0.99  ------ Input Options Time Limit: Unbounded
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ 
% 2.52/0.99  Current options:
% 2.52/0.99  ------ 
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ Proving...
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS status Theorem for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  fof(f4,axiom,(
% 2.52/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f13,plain,(
% 2.52/0.99    ! [X0] : ((v7_waybel_0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 2.52/0.99    inference(ennf_transformation,[],[f4])).
% 2.52/0.99  
% 2.52/0.99  fof(f14,plain,(
% 2.52/0.99    ! [X0] : ((v7_waybel_0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.52/0.99    inference(flattening,[],[f13])).
% 2.52/0.99  
% 2.52/0.99  fof(f24,plain,(
% 2.52/0.99    ! [X0] : (((v7_waybel_0(X0) | ? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.52/0.99    inference(nnf_transformation,[],[f14])).
% 2.52/0.99  
% 2.52/0.99  fof(f25,plain,(
% 2.52/0.99    ! [X0] : (((v7_waybel_0(X0) | ? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (? [X6] : (r1_orders_2(X0,X5,X6) & r1_orders_2(X0,X4,X6) & m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.52/0.99    inference(rectify,[],[f24])).
% 2.52/0.99  
% 2.52/0.99  fof(f28,plain,(
% 2.52/0.99    ! [X5,X4,X0] : (? [X6] : (r1_orders_2(X0,X5,X6) & r1_orders_2(X0,X4,X6) & m1_subset_1(X6,u1_struct_0(X0))) => (r1_orders_2(X0,X5,sK5(X0,X4,X5)) & r1_orders_2(X0,X4,sK5(X0,X4,X5)) & m1_subset_1(sK5(X0,X4,X5),u1_struct_0(X0))))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f27,plain,(
% 2.52/0.99    ( ! [X1] : (! [X0] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_orders_2(X0,sK4(X0),X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))) )),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f26,plain,(
% 2.52/0.99    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,sK3(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f29,plain,(
% 2.52/0.99    ! [X0] : (((v7_waybel_0(X0) | ((! [X3] : (~r1_orders_2(X0,sK4(X0),X3) | ~r1_orders_2(X0,sK3(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : ((r1_orders_2(X0,X5,sK5(X0,X4,X5)) & r1_orders_2(X0,X4,sK5(X0,X4,X5)) & m1_subset_1(sK5(X0,X4,X5),u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f28,f27,f26])).
% 2.52/0.99  
% 2.52/0.99  fof(f43,plain,(
% 2.52/0.99    ( ! [X4,X0,X5] : (m1_subset_1(sK5(X0,X4,X5),u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f29])).
% 2.52/0.99  
% 2.52/0.99  fof(f3,axiom,(
% 2.52/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f12,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 2.52/0.99    inference(ennf_transformation,[],[f3])).
% 2.52/0.99  
% 2.52/0.99  fof(f42,plain,(
% 2.52/0.99    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f12])).
% 2.52/0.99  
% 2.52/0.99  fof(f5,conjecture,(
% 2.52/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f6,negated_conjecture,(
% 2.52/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 2.52/0.99    inference(negated_conjecture,[],[f5])).
% 2.52/0.99  
% 2.52/0.99  fof(f8,plain,(
% 2.52/0.99    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 2.52/0.99    inference(pure_predicate_removal,[],[f6])).
% 2.52/0.99  
% 2.52/0.99  fof(f15,plain,(
% 2.52/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.52/0.99    inference(ennf_transformation,[],[f8])).
% 2.52/0.99  
% 2.52/0.99  fof(f16,plain,(
% 2.52/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.52/0.99    inference(flattening,[],[f15])).
% 2.52/0.99  
% 2.52/0.99  fof(f32,plain,(
% 2.52/0.99    ( ! [X0,X1] : (? [X2,X3] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2)) => (r1_xboole_0(sK8,sK9) & r1_waybel_0(X0,X1,sK9) & r1_waybel_0(X0,X1,sK8))) )),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f31,plain,(
% 2.52/0.99    ( ! [X0] : (? [X1] : (? [X2,X3] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) => (? [X3,X2] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,sK7,X3) & r1_waybel_0(X0,sK7,X2)) & l1_waybel_0(sK7,X0) & v7_waybel_0(sK7) & ~v2_struct_0(sK7))) )),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f30,plain,(
% 2.52/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X3,X2] : (r1_xboole_0(X2,X3) & r1_waybel_0(sK6,X1,X3) & r1_waybel_0(sK6,X1,X2)) & l1_waybel_0(X1,sK6) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK6) & ~v2_struct_0(sK6))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f33,plain,(
% 2.52/0.99    ((r1_xboole_0(sK8,sK9) & r1_waybel_0(sK6,sK7,sK9) & r1_waybel_0(sK6,sK7,sK8)) & l1_waybel_0(sK7,sK6) & v7_waybel_0(sK7) & ~v2_struct_0(sK7)) & l1_struct_0(sK6) & ~v2_struct_0(sK6)),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f16,f32,f31,f30])).
% 2.52/0.99  
% 2.52/0.99  fof(f53,plain,(
% 2.52/0.99    l1_waybel_0(sK7,sK6)),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f50,plain,(
% 2.52/0.99    l1_struct_0(sK6)),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f51,plain,(
% 2.52/0.99    ~v2_struct_0(sK7)),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f52,plain,(
% 2.52/0.99    v7_waybel_0(sK7)),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f45,plain,(
% 2.52/0.99    ( ! [X4,X0,X5] : (r1_orders_2(X0,X5,sK5(X0,X4,X5)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f29])).
% 2.52/0.99  
% 2.52/0.99  fof(f2,axiom,(
% 2.52/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f10,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.52/0.99    inference(ennf_transformation,[],[f2])).
% 2.52/0.99  
% 2.52/0.99  fof(f11,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.52/0.99    inference(flattening,[],[f10])).
% 2.52/0.99  
% 2.52/0.99  fof(f19,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.52/0.99    inference(nnf_transformation,[],[f11])).
% 2.52/0.99  
% 2.52/0.99  fof(f20,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.52/0.99    inference(rectify,[],[f19])).
% 2.52/0.99  
% 2.52/0.99  fof(f22,plain,(
% 2.52/0.99    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f21,plain,(
% 2.52/0.99    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f23,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3)) & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f22,f21])).
% 2.52/0.99  
% 2.52/0.99  fof(f38,plain,(
% 2.52/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f23])).
% 2.52/0.99  
% 2.52/0.99  fof(f49,plain,(
% 2.52/0.99    ~v2_struct_0(sK6)),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f37,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f23])).
% 2.52/0.99  
% 2.52/0.99  fof(f44,plain,(
% 2.52/0.99    ( ! [X4,X0,X5] : (r1_orders_2(X0,X4,sK5(X0,X4,X5)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f29])).
% 2.52/0.99  
% 2.52/0.99  fof(f1,axiom,(
% 2.52/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f7,plain,(
% 2.52/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.52/0.99    inference(rectify,[],[f1])).
% 2.52/0.99  
% 2.52/0.99  fof(f9,plain,(
% 2.52/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.52/0.99    inference(ennf_transformation,[],[f7])).
% 2.52/0.99  
% 2.52/0.99  fof(f17,plain,(
% 2.52/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f18,plain,(
% 2.52/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f17])).
% 2.52/0.99  
% 2.52/0.99  fof(f36,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f18])).
% 2.52/0.99  
% 2.52/0.99  fof(f56,plain,(
% 2.52/0.99    r1_xboole_0(sK8,sK9)),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f55,plain,(
% 2.52/0.99    r1_waybel_0(sK6,sK7,sK9)),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  fof(f54,plain,(
% 2.52/0.99    r1_waybel_0(sK6,sK7,sK8)),
% 2.52/0.99    inference(cnf_transformation,[],[f33])).
% 2.52/0.99  
% 2.52/0.99  cnf(c_14,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.52/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.52/0.99      | m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
% 2.52/0.99      | ~ v7_waybel_0(X1)
% 2.52/0.99      | ~ l1_orders_2(X1)
% 2.52/0.99      | v2_struct_0(X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_8,plain,
% 2.52/0.99      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | ~ l1_struct_0(X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_18,negated_conjecture,
% 2.52/0.99      ( l1_waybel_0(sK7,sK6) ),
% 2.52/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_357,plain,
% 2.52/0.99      ( l1_orders_2(sK7) | ~ l1_struct_0(sK6) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_8,c_18]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_21,negated_conjecture,
% 2.52/0.99      ( l1_struct_0(sK6) ),
% 2.52/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_359,plain,
% 2.52/0.99      ( l1_orders_2(sK7) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_357,c_21]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_412,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | m1_subset_1(sK5(sK7,X0,X1),u1_struct_0(sK7))
% 2.52/0.99      | ~ v7_waybel_0(sK7)
% 2.52/0.99      | v2_struct_0(sK7) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_14,c_359]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_20,negated_conjecture,
% 2.52/0.99      ( ~ v2_struct_0(sK7) ),
% 2.52/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_19,negated_conjecture,
% 2.52/0.99      ( v7_waybel_0(sK7) ),
% 2.52/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_416,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | m1_subset_1(sK5(sK7,X0,X1),u1_struct_0(sK7)) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_412,c_20,c_19]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_417,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | m1_subset_1(sK5(sK7,X1,X0),u1_struct_0(sK7)) ),
% 2.52/0.99      inference(renaming,[status(thm)],[c_416]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1091,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
% 2.52/0.99      | m1_subset_1(sK5(sK7,X1_51,X0_51),u1_struct_0(sK7)) ),
% 2.52/0.99      inference(subtyping,[status(esa)],[c_417]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_12,plain,
% 2.52/0.99      ( r1_orders_2(X0,X1,sK5(X0,X2,X1))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.52/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.52/0.99      | ~ v7_waybel_0(X0)
% 2.52/0.99      | ~ l1_orders_2(X0)
% 2.52/0.99      | v2_struct_0(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_452,plain,
% 2.52/0.99      ( r1_orders_2(sK7,X0,sK5(sK7,X1,X0))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.52/0.99      | ~ v7_waybel_0(sK7)
% 2.52/0.99      | v2_struct_0(sK7) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_12,c_359]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_454,plain,
% 2.52/0.99      ( r1_orders_2(sK7,X0,sK5(sK7,X1,X0))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_452,c_20,c_19]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1089,plain,
% 2.52/0.99      ( r1_orders_2(sK7,X0_51,sK5(sK7,X1_51,X0_51))
% 2.52/0.99      | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7)) ),
% 2.52/0.99      inference(subtyping,[status(esa)],[c_454]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_6,plain,
% 2.52/0.99      ( ~ r1_orders_2(X0,sK2(X1,X0,X2),X3)
% 2.52/0.99      | ~ r1_waybel_0(X1,X0,X2)
% 2.52/0.99      | ~ l1_waybel_0(X0,X1)
% 2.52/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.52/0.99      | r2_hidden(k2_waybel_0(X1,X0,X3),X2)
% 2.52/0.99      | ~ l1_struct_0(X1)
% 2.52/0.99      | v2_struct_0(X1)
% 2.52/0.99      | v2_struct_0(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_367,plain,
% 2.52/0.99      ( ~ r1_orders_2(sK7,sK2(sK6,sK7,X0),X1)
% 2.52/0.99      | ~ r1_waybel_0(sK6,sK7,X0)
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,X1),X0)
% 2.52/0.99      | ~ l1_struct_0(sK6)
% 2.52/0.99      | v2_struct_0(sK7)
% 2.52/0.99      | v2_struct_0(sK6) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_6,c_18]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_22,negated_conjecture,
% 2.52/0.99      ( ~ v2_struct_0(sK6) ),
% 2.52/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_371,plain,
% 2.52/0.99      ( r2_hidden(k2_waybel_0(sK6,sK7,X1),X0)
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | ~ r1_waybel_0(sK6,sK7,X0)
% 2.52/0.99      | ~ r1_orders_2(sK7,sK2(sK6,sK7,X0),X1) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_367,c_22,c_21,c_20]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_372,plain,
% 2.52/0.99      ( ~ r1_orders_2(sK7,sK2(sK6,sK7,X0),X1)
% 2.52/0.99      | ~ r1_waybel_0(sK6,sK7,X0)
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,X1),X0) ),
% 2.52/0.99      inference(renaming,[status(thm)],[c_371]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1092,plain,
% 2.52/0.99      ( ~ r1_orders_2(sK7,sK2(sK6,sK7,X0_54),X0_51)
% 2.52/0.99      | ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,X0_51),X0_54) ),
% 2.52/0.99      inference(subtyping,[status(esa)],[c_372]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1408,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(sK5(sK7,X0_51,sK2(sK6,sK7,X0_54)),u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,X0_51,sK2(sK6,sK7,X0_54))),X0_54) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_1089,c_1092]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1529,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,X0_51,sK2(sK6,sK7,X0_54))),X0_54) ),
% 2.52/0.99      inference(backward_subsumption_resolution,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_1091,c_1408]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_7,plain,
% 2.52/0.99      ( ~ r1_waybel_0(X0,X1,X2)
% 2.52/0.99      | ~ l1_waybel_0(X1,X0)
% 2.52/0.99      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 2.52/0.99      | ~ l1_struct_0(X0)
% 2.52/0.99      | v2_struct_0(X0)
% 2.52/0.99      | v2_struct_0(X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_280,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0)
% 2.52/0.99      | m1_subset_1(sK2(sK6,sK7,X0),u1_struct_0(sK7))
% 2.52/0.99      | ~ l1_struct_0(sK6)
% 2.52/0.99      | v2_struct_0(sK7)
% 2.52/0.99      | v2_struct_0(sK6) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_7,c_18]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_284,plain,
% 2.52/0.99      ( m1_subset_1(sK2(sK6,sK7,X0),u1_struct_0(sK7))
% 2.52/0.99      | ~ r1_waybel_0(sK6,sK7,X0) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_280,c_22,c_21,c_20]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_285,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0)
% 2.52/0.99      | m1_subset_1(sK2(sK6,sK7,X0),u1_struct_0(sK7)) ),
% 2.52/0.99      inference(renaming,[status(thm)],[c_284]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1096,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7)) ),
% 2.52/0.99      inference(subtyping,[status(esa)],[c_285]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3249,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,X0_51,sK2(sK6,sK7,X0_54))),X0_54) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_1529,c_1096]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3250,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,X0_51,sK2(sK6,sK7,X0_54))),X0_54) ),
% 2.52/0.99      inference(renaming,[status(thm)],[c_3249]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_13,plain,
% 2.52/0.99      ( r1_orders_2(X0,X1,sK5(X0,X1,X2))
% 2.52/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.52/0.99      | ~ v7_waybel_0(X0)
% 2.52/0.99      | ~ l1_orders_2(X0)
% 2.52/0.99      | v2_struct_0(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_432,plain,
% 2.52/0.99      ( r1_orders_2(sK7,X0,sK5(sK7,X0,X1))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 2.52/0.99      | ~ v7_waybel_0(sK7)
% 2.52/0.99      | v2_struct_0(sK7) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_13,c_359]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_436,plain,
% 2.52/0.99      ( r1_orders_2(sK7,X0,sK5(sK7,X0,X1))
% 2.52/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_432,c_20,c_19]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1090,plain,
% 2.52/0.99      ( r1_orders_2(sK7,X0_51,sK5(sK7,X0_51,X1_51))
% 2.52/0.99      | ~ m1_subset_1(X1_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7)) ),
% 2.52/0.99      inference(subtyping,[status(esa)],[c_436]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1517,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(sK5(sK7,sK2(sK6,sK7,X0_54),X0_51),u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,X0_54),X0_51)),X0_54) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_1090,c_1092]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1528,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(sK2(sK6,sK7,X0_54),u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,X0_54),X0_51)),X0_54) ),
% 2.52/0.99      inference(backward_subsumption_resolution,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_1091,c_1517]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2360,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,X0_54),X0_51)),X0_54) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_1528,c_1096]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2361,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,X0_54)
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,X0_54),X0_51)),X0_54) ),
% 2.52/0.99      inference(renaming,[status(thm)],[c_2360]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_0,plain,
% 2.52/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1102,plain,
% 2.52/0.99      ( ~ r2_hidden(X0_55,X0_54)
% 2.52/0.99      | ~ r2_hidden(X0_55,X1_54)
% 2.52/0.99      | ~ r1_xboole_0(X0_54,X1_54) ),
% 2.52/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_15,negated_conjecture,
% 2.52/0.99      ( r1_xboole_0(sK8,sK9) ),
% 2.52/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1099,negated_conjecture,
% 2.52/0.99      ( r1_xboole_0(sK8,sK9) ),
% 2.52/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1840,plain,
% 2.52/0.99      ( ~ r2_hidden(X0_55,sK9) | ~ r2_hidden(X0_55,sK8) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_1102,c_1099]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2619,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,sK9)
% 2.52/0.99      | ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,sK9),X0_51)),sK8) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_2361,c_1840]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_16,negated_conjecture,
% 2.52/0.99      ( r1_waybel_0(sK6,sK7,sK9) ),
% 2.52/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2624,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0_51,u1_struct_0(sK7))
% 2.52/0.99      | ~ r2_hidden(k2_waybel_0(sK6,sK7,sK5(sK7,sK2(sK6,sK7,sK9),X0_51)),sK8) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_2619,c_16]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3275,plain,
% 2.52/0.99      ( ~ r1_waybel_0(sK6,sK7,sK8)
% 2.52/0.99      | ~ m1_subset_1(sK2(sK6,sK7,sK9),u1_struct_0(sK7))
% 2.52/0.99      | ~ m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK7)) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_3250,c_2624]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_17,negated_conjecture,
% 2.52/0.99      ( r1_waybel_0(sK6,sK7,sK8) ),
% 2.52/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_662,plain,
% 2.52/0.99      ( m1_subset_1(sK2(sK6,sK7,sK8),u1_struct_0(sK7)) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_17,c_285]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_642,plain,
% 2.52/0.99      ( m1_subset_1(sK2(sK6,sK7,sK9),u1_struct_0(sK7)) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_16,c_285]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(contradiction,plain,
% 2.52/0.99      ( $false ),
% 2.52/0.99      inference(minisat,[status(thm)],[c_3275,c_662,c_642,c_17]) ).
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  ------                               Statistics
% 2.52/0.99  
% 2.52/0.99  ------ Selected
% 2.52/0.99  
% 2.52/0.99  total_time:                             0.145
% 2.52/0.99  
%------------------------------------------------------------------------------
