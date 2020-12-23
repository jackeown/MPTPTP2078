%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1632+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:01 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 789 expanded)
%              Number of clauses        :   73 ( 110 expanded)
%              Number of leaves         :   11 ( 281 expanded)
%              Depth                    :   17
%              Number of atoms          :  713 (9219 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_orders_2(X1,X3,X4)
                 => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  | ~ r1_orders_2(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
                  | ~ r1_orders_2(X1,X5,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f15])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
        & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
        & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          | ! [X3] :
              ( ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
                & r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
                & m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
                | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f16,f18,f17])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( r1_orders_2(X1,X3,X4)
                         => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v11_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X1))
                 => ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ( r1_orders_2(X1,X3,X4)
                           => r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2)) ) )
                      & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v11_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v11_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ m1_subset_1(X2,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f21])).

fof(f27,plain,(
    ! [X0,X1,X5] :
      ( ? [X6] :
          ( ! [X7] :
              ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
              | ~ r1_orders_2(X1,X6,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X1)) )
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ! [X7] :
            ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
            | ~ r1_orders_2(X1,sK7(X5),X7)
            | ~ m1_subset_1(X7,u1_struct_0(X1)) )
        & m1_subset_1(sK7(X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X0,X1,X3] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK6(X3)),k2_waybel_0(X0,X1,X2))
        & r1_orders_2(X1,X3,sK6(X3))
        & m1_subset_1(sK6(X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                  & r1_orders_2(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,sK5))
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,X0) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v11_waybel_0(X1,X0) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,k2_waybel_0(X0,sK4,X4),k2_waybel_0(X0,sK4,X2))
                      & r1_orders_2(sK4,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(sK4)) )
                  | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          | ~ v11_waybel_0(sK4,X0) )
        & ( ! [X5] :
              ( ? [X6] :
                  ( ! [X7] :
                      ( r1_orders_2(X0,k2_waybel_0(X0,sK4,X7),k2_waybel_0(X0,sK4,X5))
                      | ~ r1_orders_2(sK4,X6,X7)
                      | ~ m1_subset_1(X7,u1_struct_0(sK4)) )
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
          | v11_waybel_0(sK4,X0) )
        & l1_waybel_0(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,X4),k2_waybel_0(X0,X1,X2))
                          & r1_orders_2(X1,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  & m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) )
            & ( ! [X5] :
                  ( ? [X6] :
                      ( ! [X7] :
                          ( r1_orders_2(X0,k2_waybel_0(X0,X1,X7),k2_waybel_0(X0,X1,X5))
                          | ~ r1_orders_2(X1,X6,X7)
                          | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | v11_waybel_0(X1,X0) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,X1,X4),k2_waybel_0(sK3,X1,X2))
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            | ~ v11_waybel_0(X1,sK3) )
          & ( ! [X5] :
                ( ? [X6] :
                    ( ! [X7] :
                        ( r1_orders_2(sK3,k2_waybel_0(sK3,X1,X7),k2_waybel_0(sK3,X1,X5))
                        | ~ r1_orders_2(X1,X6,X7)
                        | ~ m1_subset_1(X7,u1_struct_0(X1)) )
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | v11_waybel_0(X1,sK3) )
          & l1_waybel_0(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ( ! [X3] :
            ( ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK6(X3)),k2_waybel_0(sK3,sK4,sK5))
              & r1_orders_2(sK4,X3,sK6(X3))
              & m1_subset_1(sK6(X3),u1_struct_0(sK4)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK4)) )
        & m1_subset_1(sK5,u1_struct_0(sK4)) )
      | ~ v11_waybel_0(sK4,sK3) )
    & ( ! [X5] :
          ( ( ! [X7] :
                ( r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X7),k2_waybel_0(sK3,sK4,X5))
                | ~ r1_orders_2(sK4,sK7(X5),X7)
                | ~ m1_subset_1(X7,u1_struct_0(sK4)) )
            & m1_subset_1(sK7(X5),u1_struct_0(sK4)) )
          | ~ m1_subset_1(X5,u1_struct_0(sK4)) )
      | v11_waybel_0(sK4,sK3) )
    & l1_waybel_0(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f22,f27,f26,f25,f24,f23])).

fof(f40,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X7,X5] :
      ( r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X7),k2_waybel_0(sK3,sK4,X5))
      | ~ r1_orders_2(sK4,sK7(X5),X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | v11_waybel_0(sK4,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X3] :
      ( m1_subset_1(sK6(X3),u1_struct_0(sK4))
      | ~ m1_subset_1(X3,u1_struct_0(sK4))
      | ~ v11_waybel_0(sK4,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK6(X3)),k2_waybel_0(sK3,sK4,sK5))
      | ~ m1_subset_1(X3,u1_struct_0(sK4))
      | ~ v11_waybel_0(sK4,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | r1_orders_2(X1,X3,sK1(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X3] :
      ( r1_orders_2(sK4,X3,sK6(X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK4))
      | ~ v11_waybel_0(sK4,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f33,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,k2_waybel_0(X0,X1,X6),k2_waybel_0(X0,X1,X2))
      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X5] :
      ( m1_subset_1(sK7(X5),u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | v11_waybel_0(sK4,sK3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v11_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X2] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK0(X0,X1)))
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v11_waybel_0(X1,X0)
              | ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK0(X0,X1)))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X1)) ) )
            & ( ! [X3] :
                  ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) )
              | ~ v11_waybel_0(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v11_waybel_0(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v11_waybel_0(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v11_waybel_0(X1,X0)
      | ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_3,plain,
    ( ~ r1_orders_2(X0,k2_waybel_0(X0,X1,sK1(X0,X1,X2,X3)),k2_waybel_0(X0,X1,X2))
    | r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_258,plain,
    ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),k2_waybel_0(sK3,sK4,X0))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_14])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),k2_waybel_0(sK3,sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_258,c_17,c_16,c_15])).

cnf(c_263,plain,
    ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0,X1)),k2_waybel_0(sK3,sK4,X0))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_262])).

cnf(c_1736,plain,
    ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK1(sK3,sK4,X0_47,X1_47)),k2_waybel_0(sK3,sK4,X0_47))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_263])).

cnf(c_1845,plain,
    ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK1(sK3,sK4,sK0(sK3,sK4),X0_47)),k2_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_2251,plain,
    ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK1(sK3,sK4,sK0(sK3,sK4),sK7(sK0(sK3,sK4)))),k2_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7(sK0(sK3,sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_5,plain,
    ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X0,X1,X2,X3),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_235,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4))
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_5,c_14])).

cnf(c_239,plain,
    ( m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_235,c_17,c_16,c_15])).

cnf(c_240,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_239])).

cnf(c_1737,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,X0_47,X1_47),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_240])).

cnf(c_1835,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK3,sK4,sK0(sK3,sK4),X0_47),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_2163,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | m1_subset_1(sK1(sK3,sK4,sK0(sK3,sK4),sK7(X0_47)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7(X0_47),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_2214,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | m1_subset_1(sK1(sK3,sK4,sK0(sK3,sK4),sK7(sK0(sK3,sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7(sK0(sK3,sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_12,negated_conjecture,
    ( ~ r1_orders_2(sK4,sK7(X0),X1)
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X1),k2_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1741,negated_conjecture,
    ( ~ r1_orders_2(sK4,sK7(X0_47),X1_47)
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X1_47),k2_waybel_0(sK3,sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1824,plain,
    ( ~ r1_orders_2(sK4,sK7(sK0(sK3,sK4)),X0_47)
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X0_47),k2_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_2050,plain,
    ( ~ r1_orders_2(sK4,sK7(sK0(sK3,sK4)),sK1(sK3,sK4,sK0(sK3,sK4),sK7(sK0(sK3,sK4))))
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK1(sK3,sK4,sK0(sK3,sK4),sK7(sK0(sK3,sK4)))),k2_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | ~ m1_subset_1(sK1(sK3,sK4,sK0(sK3,sK4),sK7(sK0(sK3,sK4))),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1824])).

cnf(c_10,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK6(X0),u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1743,negated_conjecture,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | m1_subset_1(sK6(X0_47),u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1996,plain,
    ( ~ m1_subset_1(sK2(sK3,sK4,sK5),u1_struct_0(sK4))
    | m1_subset_1(sK6(sK2(sK3,sK4,sK5)),u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1743])).

cnf(c_8,negated_conjecture,
    ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK6(X0)),k2_waybel_0(sK3,sK4,sK5))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1745,negated_conjecture,
    ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK6(X0_47)),k2_waybel_0(sK3,sK4,sK5))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1975,plain,
    ( ~ r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK6(sK2(sK3,sK4,sK5))),k2_waybel_0(sK3,sK4,sK5))
    | ~ m1_subset_1(sK2(sK3,sK4,sK5),u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_4,plain,
    ( r1_orders_2(X0,X1,sK1(X2,X0,X3,X1))
    | r1_waybel_0(X2,X0,a_3_1_waybel_0(X2,X0,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,X2)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_327,plain,
    ( r1_orders_2(sK4,X0,sK1(sK3,sK4,X1,X0))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_4,c_14])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X1))
    | r1_orders_2(sK4,X0,sK1(sK3,sK4,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_17,c_16,c_15])).

cnf(c_332,plain,
    ( r1_orders_2(sK4,X0,sK1(sK3,sK4,X1,X0))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_1732,plain,
    ( r1_orders_2(sK4,X0_47,sK1(sK3,sK4,X1_47,X0_47))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X1_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_332])).

cnf(c_1857,plain,
    ( r1_orders_2(sK4,sK7(sK0(sK3,sK4)),sK1(sK3,sK4,X0_47,sK7(sK0(sK3,sK4))))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7(sK0(sK3,sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_1966,plain,
    ( r1_orders_2(sK4,sK7(sK0(sK3,sK4)),sK1(sK3,sK4,sK0(sK3,sK4),sK7(sK0(sK3,sK4))))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | ~ m1_subset_1(sK7(sK0(sK3,sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1857])).

cnf(c_9,negated_conjecture,
    ( r1_orders_2(sK4,X0,sK6(X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1744,negated_conjecture,
    ( r1_orders_2(sK4,X0_47,sK6(X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1942,plain,
    ( r1_orders_2(sK4,sK2(sK3,sK4,X0_47),sK6(sK2(sK3,sK4,X0_47)))
    | ~ m1_subset_1(sK2(sK3,sK4,X0_47),u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_1948,plain,
    ( r1_orders_2(sK4,sK2(sK3,sK4,sK5),sK6(sK2(sK3,sK4,sK5)))
    | ~ m1_subset_1(sK2(sK3,sK4,sK5),u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_6,plain,
    ( ~ r1_orders_2(X0,sK2(X1,X0,X2),X3)
    | r1_orders_2(X1,k2_waybel_0(X1,X0,X3),k2_waybel_0(X1,X0,X2))
    | ~ r1_waybel_0(X1,X0,a_3_1_waybel_0(X1,X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_189,plain,
    ( ~ r1_orders_2(sK4,sK2(sK3,sK4,X0),X1)
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X1),k2_waybel_0(sK3,sK4,X0))
    | ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_6,c_14])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X1),k2_waybel_0(sK3,sK4,X0))
    | ~ r1_orders_2(sK4,sK2(sK3,sK4,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_189,c_17,c_16,c_15])).

cnf(c_194,plain,
    ( ~ r1_orders_2(sK4,sK2(sK3,sK4,X0),X1)
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X1),k2_waybel_0(sK3,sK4,X0))
    | ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_1739,plain,
    ( ~ r1_orders_2(sK4,sK2(sK3,sK4,X0_47),X1_47)
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,X1_47),k2_waybel_0(sK3,sK4,X0_47))
    | ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_47,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_1941,plain,
    ( ~ r1_orders_2(sK4,sK2(sK3,sK4,X0_47),sK6(sK2(sK3,sK4,X0_47)))
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK6(sK2(sK3,sK4,X0_47))),k2_waybel_0(sK3,sK4,X0_47))
    | ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6(sK2(sK3,sK4,X0_47)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_1944,plain,
    ( ~ r1_orders_2(sK4,sK2(sK3,sK4,sK5),sK6(sK2(sK3,sK4,sK5)))
    | r1_orders_2(sK3,k2_waybel_0(sK3,sK4,sK6(sK2(sK3,sK4,sK5))),k2_waybel_0(sK3,sK4,sK5))
    | ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK5))
    | ~ m1_subset_1(sK6(sK2(sK3,sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_13,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK7(X0),u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1740,negated_conjecture,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | m1_subset_1(sK7(X0_47),u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1825,plain,
    ( ~ m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | m1_subset_1(sK7(sK0(sK3,sK4)),u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_2,plain,
    ( r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v11_waybel_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_281,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_2,c_14])).

cnf(c_285,plain,
    ( ~ v11_waybel_0(sK4,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_281,c_17,c_16,c_15])).

cnf(c_286,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_285])).

cnf(c_1735,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_286])).

cnf(c_1775,plain,
    ( r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK5))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1735])).

cnf(c_7,plain,
    ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_215,plain,
    ( ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK3,sK4,X0),u1_struct_0(sK4))
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_7,c_14])).

cnf(c_219,plain,
    ( m1_subset_1(sK2(sK3,sK4,X0),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_215,c_17,c_16,c_15])).

cnf(c_220,plain,
    ( ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK3,sK4,X0),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_219])).

cnf(c_1738,plain,
    ( ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,X0_47))
    | ~ m1_subset_1(X0_47,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK3,sK4,X0_47),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_220])).

cnf(c_1766,plain,
    ( ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK5))
    | m1_subset_1(sK2(sK3,sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X0)
    | v11_waybel_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_301,plain,
    ( m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_1,c_14])).

cnf(c_303,plain,
    ( v11_waybel_0(sK4,sK3)
    | m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_17,c_16,c_15])).

cnf(c_304,plain,
    ( m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | v11_waybel_0(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ v11_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_726,plain,
    ( m1_subset_1(sK0(sK3,sK4),u1_struct_0(sK4))
    | m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_304,c_11])).

cnf(c_0,plain,
    ( ~ r1_waybel_0(X0,X1,a_3_1_waybel_0(X0,X1,sK0(X0,X1)))
    | ~ l1_waybel_0(X1,X0)
    | v11_waybel_0(X1,X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_314,plain,
    ( ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | v11_waybel_0(sK4,sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_0,c_14])).

cnf(c_316,plain,
    ( v11_waybel_0(sK4,sK3)
    | ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_17,c_16,c_15])).

cnf(c_317,plain,
    ( ~ r1_waybel_0(sK3,sK4,a_3_1_waybel_0(sK3,sK4,sK0(sK3,sK4)))
    | v11_waybel_0(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_316])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2251,c_2214,c_2050,c_1996,c_1975,c_1966,c_1948,c_1944,c_1825,c_1775,c_1766,c_726,c_317,c_304,c_11])).


%------------------------------------------------------------------------------
