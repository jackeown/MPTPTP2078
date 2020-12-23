%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:05 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 252 expanded)
%              Number of clauses        :   47 (  52 expanded)
%              Number of leaves         :   12 ( 116 expanded)
%              Depth                    :   20
%              Number of atoms          :  444 (2623 expanded)
%              Number of equality atoms :   73 ( 573 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X2,X5,X6)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_waybel_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_6(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X2,X5,X6)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X3,X4)
          & r1_orders_2(X2,X5,X6)
          & X4 = X6
          & X3 = X5
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X1,X3,X4)
        & r1_orders_2(X2,X5,sK6)
        & sK6 = X4
        & X3 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(X1,X3,X4)
              & r1_orders_2(X2,X5,X6)
              & X4 = X6
              & X3 = X5
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( ? [X6] :
            ( ~ r1_orders_2(X1,X3,X4)
            & r1_orders_2(X2,sK5,X6)
            & X4 = X6
            & sK5 = X3
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(X1,X3,X4)
                  & r1_orders_2(X2,X5,X6)
                  & X4 = X6
                  & X3 = X5
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X2)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(X1,X3,sK4)
                & r1_orders_2(X2,X5,X6)
                & sK4 = X6
                & X3 = X5
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(X1,X3,X4)
                      & r1_orders_2(X2,X5,X6)
                      & X4 = X6
                      & X3 = X5
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X2)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(X1,sK3,X4)
                    & r1_orders_2(X2,X5,X6)
                    & X4 = X6
                    & sK3 = X5
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_orders_2(X1,X3,X4)
                          & r1_orders_2(X2,X5,X6)
                          & X4 = X6
                          & X3 = X5
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_yellow_6(X2,X0,X1) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(X1,X3,X4)
                        & r1_orders_2(sK2,X5,X6)
                        & X4 = X6
                        & X3 = X5
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(sK2)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_yellow_6(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_orders_2(sK1,X3,X4)
                            & r1_orders_2(X2,X5,X6)
                            & X4 = X6
                            & X3 = X5
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_yellow_6(X2,X0,sK1) )
        & l1_waybel_0(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_orders_2(X1,X3,X4)
                                & r1_orders_2(X2,X5,X6)
                                & X4 = X6
                                & X3 = X5
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X1,X3,X4)
                              & r1_orders_2(X2,X5,X6)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,sK0,X1) )
          & l1_waybel_0(X1,sK0) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_orders_2(sK1,sK3,sK4)
    & r1_orders_2(sK2,sK5,sK6)
    & sK4 = sK6
    & sK3 = sK5
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_yellow_6(sK2,sK0,sK1)
    & l1_waybel_0(sK1,sK0)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f23,f22,f21,f20,f19,f18,f17])).

fof(f33,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f43,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X0,X4,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow_6(X2,X0,X1)
                  | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  | ~ m1_yellow_0(X2,X1) )
                & ( ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                    & m1_yellow_0(X2,X1) )
                  | ~ m1_yellow_6(X2,X0,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ~ r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_14,negated_conjecture,
    ( m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_16,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_267,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_268,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_yellow_0(X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_300,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ l1_waybel_0(X4,sK0)
    | ~ m1_yellow_0(X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | X3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_268,c_0])).

cnf(c_301,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ l1_waybel_0(X3,sK0)
    | ~ m1_yellow_0(X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_4,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_81,plain,
    ( ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X0,X1,X2)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_5])).

cnf(c_82,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_81])).

cnf(c_218,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_82,c_16])).

cnf(c_219,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ l1_waybel_0(X1,sK0)
    | m1_yellow_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_338,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | r1_orders_2(X5,X3,X4)
    | ~ l1_waybel_0(X5,sK0)
    | ~ l1_waybel_0(X1,sK0)
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X3,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X1 != X5
    | X0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_301,c_219])).

cnf(c_339,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X1,X2,X3)
    | ~ l1_waybel_0(X1,sK0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_375,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ l1_waybel_0(X3,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | sK0 != sK0
    | sK2 != X0
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_339])).

cnf(c_376,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK1,X0,X1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_15,negated_conjecture,
    ( l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_380,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_15])).

cnf(c_381,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_380])).

cnf(c_485,plain,
    ( ~ r1_orders_2(sK2,X0_48,X1_48)
    | r1_orders_2(sK1,X0_48,X1_48)
    | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_740,plain,
    ( ~ r1_orders_2(sK2,X0_48,sK4)
    | r1_orders_2(sK1,X0_48,sK4)
    | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_742,plain,
    ( ~ r1_orders_2(sK2,sK3,sK4)
    | r1_orders_2(sK1,sK3,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_7,negated_conjecture,
    ( r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_492,negated_conjecture,
    ( r1_orders_2(sK2,sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_635,plain,
    ( r1_orders_2(sK2,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_9,negated_conjecture,
    ( sK3 = sK5 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_490,negated_conjecture,
    ( sK3 = sK5 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_8,negated_conjecture,
    ( sK4 = sK6 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_491,negated_conjecture,
    ( sK4 = sK6 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_645,plain,
    ( r1_orders_2(sK2,sK3,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_635,c_490,c_491])).

cnf(c_680,plain,
    ( r1_orders_2(sK2,sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_645])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_489,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_636,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_648,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_636,c_491])).

cnf(c_679,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_648])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_488,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_637,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_651,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_637,c_490])).

cnf(c_674,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_651])).

cnf(c_6,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_742,c_680,c_679,c_674,c_6,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:45:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.81/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.81/0.99  
% 0.81/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.81/0.99  
% 0.81/0.99  ------  iProver source info
% 0.81/0.99  
% 0.81/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.81/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.81/0.99  git: non_committed_changes: false
% 0.81/0.99  git: last_make_outside_of_git: false
% 0.81/0.99  
% 0.81/0.99  ------ 
% 0.81/0.99  
% 0.81/0.99  ------ Input Options
% 0.81/0.99  
% 0.81/0.99  --out_options                           all
% 0.81/0.99  --tptp_safe_out                         true
% 0.81/0.99  --problem_path                          ""
% 0.81/0.99  --include_path                          ""
% 0.81/0.99  --clausifier                            res/vclausify_rel
% 0.81/0.99  --clausifier_options                    --mode clausify
% 0.81/0.99  --stdin                                 false
% 0.81/0.99  --stats_out                             all
% 0.81/0.99  
% 0.81/0.99  ------ General Options
% 0.81/0.99  
% 0.81/0.99  --fof                                   false
% 0.81/0.99  --time_out_real                         305.
% 0.81/0.99  --time_out_virtual                      -1.
% 0.81/0.99  --symbol_type_check                     false
% 0.81/0.99  --clausify_out                          false
% 0.81/0.99  --sig_cnt_out                           false
% 0.81/0.99  --trig_cnt_out                          false
% 0.81/0.99  --trig_cnt_out_tolerance                1.
% 0.81/0.99  --trig_cnt_out_sk_spl                   false
% 0.81/0.99  --abstr_cl_out                          false
% 0.81/0.99  
% 0.81/0.99  ------ Global Options
% 0.81/0.99  
% 0.81/0.99  --schedule                              default
% 0.81/0.99  --add_important_lit                     false
% 0.81/0.99  --prop_solver_per_cl                    1000
% 0.81/0.99  --min_unsat_core                        false
% 0.81/0.99  --soft_assumptions                      false
% 0.81/0.99  --soft_lemma_size                       3
% 0.81/0.99  --prop_impl_unit_size                   0
% 0.81/0.99  --prop_impl_unit                        []
% 0.81/0.99  --share_sel_clauses                     true
% 0.81/0.99  --reset_solvers                         false
% 0.81/0.99  --bc_imp_inh                            [conj_cone]
% 0.81/0.99  --conj_cone_tolerance                   3.
% 0.81/0.99  --extra_neg_conj                        none
% 0.81/0.99  --large_theory_mode                     true
% 0.81/0.99  --prolific_symb_bound                   200
% 0.81/0.99  --lt_threshold                          2000
% 0.81/0.99  --clause_weak_htbl                      true
% 0.81/0.99  --gc_record_bc_elim                     false
% 0.81/0.99  
% 0.81/0.99  ------ Preprocessing Options
% 0.81/0.99  
% 0.81/0.99  --preprocessing_flag                    true
% 0.81/0.99  --time_out_prep_mult                    0.1
% 0.81/0.99  --splitting_mode                        input
% 0.81/0.99  --splitting_grd                         true
% 0.81/0.99  --splitting_cvd                         false
% 0.81/0.99  --splitting_cvd_svl                     false
% 0.81/0.99  --splitting_nvd                         32
% 0.81/0.99  --sub_typing                            true
% 0.81/0.99  --prep_gs_sim                           true
% 0.81/0.99  --prep_unflatten                        true
% 0.81/0.99  --prep_res_sim                          true
% 0.81/0.99  --prep_upred                            true
% 0.81/0.99  --prep_sem_filter                       exhaustive
% 0.81/0.99  --prep_sem_filter_out                   false
% 0.81/0.99  --pred_elim                             true
% 0.81/0.99  --res_sim_input                         true
% 0.81/0.99  --eq_ax_congr_red                       true
% 0.81/0.99  --pure_diseq_elim                       true
% 0.81/0.99  --brand_transform                       false
% 0.81/0.99  --non_eq_to_eq                          false
% 0.81/0.99  --prep_def_merge                        true
% 0.81/0.99  --prep_def_merge_prop_impl              false
% 0.81/0.99  --prep_def_merge_mbd                    true
% 0.81/0.99  --prep_def_merge_tr_red                 false
% 0.81/0.99  --prep_def_merge_tr_cl                  false
% 0.81/0.99  --smt_preprocessing                     true
% 0.81/0.99  --smt_ac_axioms                         fast
% 0.81/0.99  --preprocessed_out                      false
% 0.81/0.99  --preprocessed_stats                    false
% 0.81/0.99  
% 0.81/0.99  ------ Abstraction refinement Options
% 0.81/0.99  
% 0.81/0.99  --abstr_ref                             []
% 0.81/0.99  --abstr_ref_prep                        false
% 0.81/0.99  --abstr_ref_until_sat                   false
% 0.81/0.99  --abstr_ref_sig_restrict                funpre
% 0.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.81/0.99  --abstr_ref_under                       []
% 0.81/0.99  
% 0.81/0.99  ------ SAT Options
% 0.81/0.99  
% 0.81/0.99  --sat_mode                              false
% 0.81/0.99  --sat_fm_restart_options                ""
% 0.81/0.99  --sat_gr_def                            false
% 0.81/0.99  --sat_epr_types                         true
% 0.81/0.99  --sat_non_cyclic_types                  false
% 0.81/0.99  --sat_finite_models                     false
% 0.81/0.99  --sat_fm_lemmas                         false
% 0.81/0.99  --sat_fm_prep                           false
% 0.81/0.99  --sat_fm_uc_incr                        true
% 0.81/0.99  --sat_out_model                         small
% 0.81/0.99  --sat_out_clauses                       false
% 0.81/0.99  
% 0.81/0.99  ------ QBF Options
% 0.81/0.99  
% 0.81/0.99  --qbf_mode                              false
% 0.81/0.99  --qbf_elim_univ                         false
% 0.81/0.99  --qbf_dom_inst                          none
% 0.81/0.99  --qbf_dom_pre_inst                      false
% 0.81/0.99  --qbf_sk_in                             false
% 0.81/0.99  --qbf_pred_elim                         true
% 0.81/0.99  --qbf_split                             512
% 0.81/0.99  
% 0.81/0.99  ------ BMC1 Options
% 0.81/0.99  
% 0.81/0.99  --bmc1_incremental                      false
% 0.81/0.99  --bmc1_axioms                           reachable_all
% 0.81/0.99  --bmc1_min_bound                        0
% 0.81/0.99  --bmc1_max_bound                        -1
% 0.81/0.99  --bmc1_max_bound_default                -1
% 0.81/0.99  --bmc1_symbol_reachability              true
% 0.81/0.99  --bmc1_property_lemmas                  false
% 0.81/0.99  --bmc1_k_induction                      false
% 0.81/0.99  --bmc1_non_equiv_states                 false
% 0.81/0.99  --bmc1_deadlock                         false
% 0.81/0.99  --bmc1_ucm                              false
% 0.81/0.99  --bmc1_add_unsat_core                   none
% 0.81/0.99  --bmc1_unsat_core_children              false
% 0.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.81/0.99  --bmc1_out_stat                         full
% 0.81/0.99  --bmc1_ground_init                      false
% 0.81/0.99  --bmc1_pre_inst_next_state              false
% 0.81/0.99  --bmc1_pre_inst_state                   false
% 0.81/0.99  --bmc1_pre_inst_reach_state             false
% 0.81/0.99  --bmc1_out_unsat_core                   false
% 0.81/0.99  --bmc1_aig_witness_out                  false
% 0.81/0.99  --bmc1_verbose                          false
% 0.81/0.99  --bmc1_dump_clauses_tptp                false
% 0.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.81/0.99  --bmc1_dump_file                        -
% 0.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.81/0.99  --bmc1_ucm_extend_mode                  1
% 0.81/0.99  --bmc1_ucm_init_mode                    2
% 0.81/0.99  --bmc1_ucm_cone_mode                    none
% 0.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.81/0.99  --bmc1_ucm_relax_model                  4
% 0.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.81/0.99  --bmc1_ucm_layered_model                none
% 0.81/0.99  --bmc1_ucm_max_lemma_size               10
% 0.81/0.99  
% 0.81/0.99  ------ AIG Options
% 0.81/0.99  
% 0.81/0.99  --aig_mode                              false
% 0.81/0.99  
% 0.81/0.99  ------ Instantiation Options
% 0.81/0.99  
% 0.81/0.99  --instantiation_flag                    true
% 0.81/0.99  --inst_sos_flag                         false
% 0.81/0.99  --inst_sos_phase                        true
% 0.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.81/0.99  --inst_lit_sel_side                     num_symb
% 0.81/0.99  --inst_solver_per_active                1400
% 0.81/0.99  --inst_solver_calls_frac                1.
% 0.81/0.99  --inst_passive_queue_type               priority_queues
% 0.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.81/0.99  --inst_passive_queues_freq              [25;2]
% 0.81/0.99  --inst_dismatching                      true
% 0.81/0.99  --inst_eager_unprocessed_to_passive     true
% 0.81/0.99  --inst_prop_sim_given                   true
% 0.81/0.99  --inst_prop_sim_new                     false
% 0.81/0.99  --inst_subs_new                         false
% 0.81/0.99  --inst_eq_res_simp                      false
% 0.81/0.99  --inst_subs_given                       false
% 0.81/0.99  --inst_orphan_elimination               true
% 0.81/0.99  --inst_learning_loop_flag               true
% 0.81/0.99  --inst_learning_start                   3000
% 0.81/0.99  --inst_learning_factor                  2
% 0.81/0.99  --inst_start_prop_sim_after_learn       3
% 0.81/0.99  --inst_sel_renew                        solver
% 0.81/0.99  --inst_lit_activity_flag                true
% 0.81/0.99  --inst_restr_to_given                   false
% 0.81/0.99  --inst_activity_threshold               500
% 0.81/0.99  --inst_out_proof                        true
% 0.81/0.99  
% 0.81/0.99  ------ Resolution Options
% 0.81/0.99  
% 0.81/0.99  --resolution_flag                       true
% 0.81/0.99  --res_lit_sel                           adaptive
% 0.81/0.99  --res_lit_sel_side                      none
% 0.81/0.99  --res_ordering                          kbo
% 0.81/0.99  --res_to_prop_solver                    active
% 0.81/0.99  --res_prop_simpl_new                    false
% 0.81/0.99  --res_prop_simpl_given                  true
% 0.81/0.99  --res_passive_queue_type                priority_queues
% 0.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.81/0.99  --res_passive_queues_freq               [15;5]
% 0.81/0.99  --res_forward_subs                      full
% 0.81/0.99  --res_backward_subs                     full
% 0.81/0.99  --res_forward_subs_resolution           true
% 0.81/0.99  --res_backward_subs_resolution          true
% 0.81/0.99  --res_orphan_elimination                true
% 0.81/0.99  --res_time_limit                        2.
% 0.81/0.99  --res_out_proof                         true
% 0.81/0.99  
% 0.81/0.99  ------ Superposition Options
% 0.81/0.99  
% 0.81/0.99  --superposition_flag                    true
% 0.81/0.99  --sup_passive_queue_type                priority_queues
% 0.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.81/0.99  --demod_completeness_check              fast
% 0.81/0.99  --demod_use_ground                      true
% 0.81/0.99  --sup_to_prop_solver                    passive
% 0.81/0.99  --sup_prop_simpl_new                    true
% 0.81/0.99  --sup_prop_simpl_given                  true
% 0.81/0.99  --sup_fun_splitting                     false
% 0.81/0.99  --sup_smt_interval                      50000
% 0.81/0.99  
% 0.81/0.99  ------ Superposition Simplification Setup
% 0.81/0.99  
% 0.81/0.99  --sup_indices_passive                   []
% 0.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.99  --sup_full_bw                           [BwDemod]
% 0.81/0.99  --sup_immed_triv                        [TrivRules]
% 0.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.99  --sup_immed_bw_main                     []
% 0.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.99  
% 0.81/0.99  ------ Combination Options
% 0.81/0.99  
% 0.81/0.99  --comb_res_mult                         3
% 0.81/0.99  --comb_sup_mult                         2
% 0.81/0.99  --comb_inst_mult                        10
% 0.81/0.99  
% 0.81/0.99  ------ Debug Options
% 0.81/0.99  
% 0.81/0.99  --dbg_backtrace                         false
% 0.81/0.99  --dbg_dump_prop_clauses                 false
% 0.81/0.99  --dbg_dump_prop_clauses_file            -
% 0.81/0.99  --dbg_out_stat                          false
% 0.81/0.99  ------ Parsing...
% 0.81/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.81/0.99  
% 0.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.81/0.99  
% 0.81/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.81/0.99  
% 0.81/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.81/0.99  ------ Proving...
% 0.81/0.99  ------ Problem Properties 
% 0.81/0.99  
% 0.81/0.99  
% 0.81/0.99  clauses                                 10
% 0.81/0.99  conjectures                             8
% 0.81/0.99  EPR                                     4
% 0.81/0.99  Horn                                    10
% 0.81/0.99  unary                                   9
% 0.81/0.99  binary                                  0
% 0.81/0.99  lits                                    15
% 0.81/0.99  lits eq                                 3
% 0.81/0.99  fd_pure                                 0
% 0.81/0.99  fd_pseudo                               0
% 0.81/0.99  fd_cond                                 0
% 0.81/0.99  fd_pseudo_cond                          0
% 0.81/0.99  AC symbols                              0
% 0.81/0.99  
% 0.81/0.99  ------ Schedule dynamic 5 is on 
% 0.81/0.99  
% 0.81/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.81/0.99  
% 0.81/0.99  
% 0.81/0.99  ------ 
% 0.81/0.99  Current options:
% 0.81/0.99  ------ 
% 0.81/0.99  
% 0.81/0.99  ------ Input Options
% 0.81/0.99  
% 0.81/0.99  --out_options                           all
% 0.81/0.99  --tptp_safe_out                         true
% 0.81/0.99  --problem_path                          ""
% 0.81/0.99  --include_path                          ""
% 0.81/0.99  --clausifier                            res/vclausify_rel
% 0.81/0.99  --clausifier_options                    --mode clausify
% 0.81/0.99  --stdin                                 false
% 0.81/0.99  --stats_out                             all
% 0.81/0.99  
% 0.81/0.99  ------ General Options
% 0.81/0.99  
% 0.81/0.99  --fof                                   false
% 0.81/0.99  --time_out_real                         305.
% 0.81/0.99  --time_out_virtual                      -1.
% 0.81/0.99  --symbol_type_check                     false
% 0.81/0.99  --clausify_out                          false
% 0.81/0.99  --sig_cnt_out                           false
% 0.81/0.99  --trig_cnt_out                          false
% 0.81/0.99  --trig_cnt_out_tolerance                1.
% 0.81/0.99  --trig_cnt_out_sk_spl                   false
% 0.81/0.99  --abstr_cl_out                          false
% 0.81/0.99  
% 0.81/0.99  ------ Global Options
% 0.81/0.99  
% 0.81/0.99  --schedule                              default
% 0.81/0.99  --add_important_lit                     false
% 0.81/0.99  --prop_solver_per_cl                    1000
% 0.81/0.99  --min_unsat_core                        false
% 0.81/0.99  --soft_assumptions                      false
% 0.81/0.99  --soft_lemma_size                       3
% 0.81/0.99  --prop_impl_unit_size                   0
% 0.81/0.99  --prop_impl_unit                        []
% 0.81/0.99  --share_sel_clauses                     true
% 0.81/0.99  --reset_solvers                         false
% 0.81/0.99  --bc_imp_inh                            [conj_cone]
% 0.81/0.99  --conj_cone_tolerance                   3.
% 0.81/0.99  --extra_neg_conj                        none
% 0.81/0.99  --large_theory_mode                     true
% 0.81/0.99  --prolific_symb_bound                   200
% 0.81/0.99  --lt_threshold                          2000
% 0.81/0.99  --clause_weak_htbl                      true
% 0.81/0.99  --gc_record_bc_elim                     false
% 0.81/0.99  
% 0.81/0.99  ------ Preprocessing Options
% 0.81/0.99  
% 0.81/0.99  --preprocessing_flag                    true
% 0.81/0.99  --time_out_prep_mult                    0.1
% 0.81/0.99  --splitting_mode                        input
% 0.81/0.99  --splitting_grd                         true
% 0.81/0.99  --splitting_cvd                         false
% 0.81/0.99  --splitting_cvd_svl                     false
% 0.81/0.99  --splitting_nvd                         32
% 0.81/0.99  --sub_typing                            true
% 0.81/0.99  --prep_gs_sim                           true
% 0.81/0.99  --prep_unflatten                        true
% 0.81/0.99  --prep_res_sim                          true
% 0.81/0.99  --prep_upred                            true
% 0.81/0.99  --prep_sem_filter                       exhaustive
% 0.81/0.99  --prep_sem_filter_out                   false
% 0.81/0.99  --pred_elim                             true
% 0.81/0.99  --res_sim_input                         true
% 0.81/0.99  --eq_ax_congr_red                       true
% 0.81/0.99  --pure_diseq_elim                       true
% 0.81/0.99  --brand_transform                       false
% 0.81/0.99  --non_eq_to_eq                          false
% 0.81/0.99  --prep_def_merge                        true
% 0.81/0.99  --prep_def_merge_prop_impl              false
% 0.81/0.99  --prep_def_merge_mbd                    true
% 0.81/0.99  --prep_def_merge_tr_red                 false
% 0.81/0.99  --prep_def_merge_tr_cl                  false
% 0.81/0.99  --smt_preprocessing                     true
% 0.81/0.99  --smt_ac_axioms                         fast
% 0.81/0.99  --preprocessed_out                      false
% 0.81/0.99  --preprocessed_stats                    false
% 0.81/0.99  
% 0.81/0.99  ------ Abstraction refinement Options
% 0.81/0.99  
% 0.81/0.99  --abstr_ref                             []
% 0.81/0.99  --abstr_ref_prep                        false
% 0.81/0.99  --abstr_ref_until_sat                   false
% 0.81/0.99  --abstr_ref_sig_restrict                funpre
% 0.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.81/0.99  --abstr_ref_under                       []
% 0.81/0.99  
% 0.81/0.99  ------ SAT Options
% 0.81/0.99  
% 0.81/0.99  --sat_mode                              false
% 0.81/0.99  --sat_fm_restart_options                ""
% 0.81/0.99  --sat_gr_def                            false
% 0.81/0.99  --sat_epr_types                         true
% 0.81/0.99  --sat_non_cyclic_types                  false
% 0.81/0.99  --sat_finite_models                     false
% 0.81/0.99  --sat_fm_lemmas                         false
% 0.81/0.99  --sat_fm_prep                           false
% 0.81/0.99  --sat_fm_uc_incr                        true
% 0.81/0.99  --sat_out_model                         small
% 0.81/0.99  --sat_out_clauses                       false
% 0.81/0.99  
% 0.81/0.99  ------ QBF Options
% 0.81/0.99  
% 0.81/0.99  --qbf_mode                              false
% 0.81/0.99  --qbf_elim_univ                         false
% 0.81/0.99  --qbf_dom_inst                          none
% 0.81/0.99  --qbf_dom_pre_inst                      false
% 0.81/0.99  --qbf_sk_in                             false
% 0.81/0.99  --qbf_pred_elim                         true
% 0.81/0.99  --qbf_split                             512
% 0.81/0.99  
% 0.81/0.99  ------ BMC1 Options
% 0.81/0.99  
% 0.81/0.99  --bmc1_incremental                      false
% 0.81/0.99  --bmc1_axioms                           reachable_all
% 0.81/0.99  --bmc1_min_bound                        0
% 0.81/0.99  --bmc1_max_bound                        -1
% 0.81/0.99  --bmc1_max_bound_default                -1
% 0.81/0.99  --bmc1_symbol_reachability              true
% 0.81/0.99  --bmc1_property_lemmas                  false
% 0.81/0.99  --bmc1_k_induction                      false
% 0.81/0.99  --bmc1_non_equiv_states                 false
% 0.81/0.99  --bmc1_deadlock                         false
% 0.81/0.99  --bmc1_ucm                              false
% 0.81/0.99  --bmc1_add_unsat_core                   none
% 0.81/0.99  --bmc1_unsat_core_children              false
% 0.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.81/0.99  --bmc1_out_stat                         full
% 0.81/0.99  --bmc1_ground_init                      false
% 0.81/0.99  --bmc1_pre_inst_next_state              false
% 0.81/0.99  --bmc1_pre_inst_state                   false
% 0.81/0.99  --bmc1_pre_inst_reach_state             false
% 0.81/0.99  --bmc1_out_unsat_core                   false
% 0.81/0.99  --bmc1_aig_witness_out                  false
% 0.81/0.99  --bmc1_verbose                          false
% 0.81/0.99  --bmc1_dump_clauses_tptp                false
% 0.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.81/0.99  --bmc1_dump_file                        -
% 0.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.81/0.99  --bmc1_ucm_extend_mode                  1
% 0.81/0.99  --bmc1_ucm_init_mode                    2
% 0.81/0.99  --bmc1_ucm_cone_mode                    none
% 0.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.81/0.99  --bmc1_ucm_relax_model                  4
% 0.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.81/0.99  --bmc1_ucm_layered_model                none
% 0.81/0.99  --bmc1_ucm_max_lemma_size               10
% 0.81/0.99  
% 0.81/0.99  ------ AIG Options
% 0.81/0.99  
% 0.81/0.99  --aig_mode                              false
% 0.81/0.99  
% 0.81/0.99  ------ Instantiation Options
% 0.81/0.99  
% 0.81/0.99  --instantiation_flag                    true
% 0.81/0.99  --inst_sos_flag                         false
% 0.81/0.99  --inst_sos_phase                        true
% 0.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.81/0.99  --inst_lit_sel_side                     none
% 0.81/0.99  --inst_solver_per_active                1400
% 0.81/0.99  --inst_solver_calls_frac                1.
% 0.81/0.99  --inst_passive_queue_type               priority_queues
% 0.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.81/0.99  --inst_passive_queues_freq              [25;2]
% 0.81/0.99  --inst_dismatching                      true
% 0.81/0.99  --inst_eager_unprocessed_to_passive     true
% 0.81/0.99  --inst_prop_sim_given                   true
% 0.81/0.99  --inst_prop_sim_new                     false
% 0.81/0.99  --inst_subs_new                         false
% 0.81/0.99  --inst_eq_res_simp                      false
% 0.81/0.99  --inst_subs_given                       false
% 0.81/0.99  --inst_orphan_elimination               true
% 0.81/0.99  --inst_learning_loop_flag               true
% 0.81/0.99  --inst_learning_start                   3000
% 0.81/0.99  --inst_learning_factor                  2
% 0.81/0.99  --inst_start_prop_sim_after_learn       3
% 0.81/0.99  --inst_sel_renew                        solver
% 0.81/0.99  --inst_lit_activity_flag                true
% 0.81/0.99  --inst_restr_to_given                   false
% 0.81/0.99  --inst_activity_threshold               500
% 0.81/0.99  --inst_out_proof                        true
% 0.81/0.99  
% 0.81/0.99  ------ Resolution Options
% 0.81/0.99  
% 0.81/0.99  --resolution_flag                       false
% 0.81/0.99  --res_lit_sel                           adaptive
% 0.81/0.99  --res_lit_sel_side                      none
% 0.81/0.99  --res_ordering                          kbo
% 0.81/0.99  --res_to_prop_solver                    active
% 0.81/0.99  --res_prop_simpl_new                    false
% 0.81/0.99  --res_prop_simpl_given                  true
% 0.81/0.99  --res_passive_queue_type                priority_queues
% 0.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.81/0.99  --res_passive_queues_freq               [15;5]
% 0.81/0.99  --res_forward_subs                      full
% 0.81/0.99  --res_backward_subs                     full
% 0.81/0.99  --res_forward_subs_resolution           true
% 0.81/0.99  --res_backward_subs_resolution          true
% 0.81/0.99  --res_orphan_elimination                true
% 0.81/0.99  --res_time_limit                        2.
% 0.81/0.99  --res_out_proof                         true
% 0.81/0.99  
% 0.81/0.99  ------ Superposition Options
% 0.81/0.99  
% 0.81/0.99  --superposition_flag                    true
% 0.81/0.99  --sup_passive_queue_type                priority_queues
% 0.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.81/0.99  --demod_completeness_check              fast
% 0.81/0.99  --demod_use_ground                      true
% 0.81/0.99  --sup_to_prop_solver                    passive
% 0.81/0.99  --sup_prop_simpl_new                    true
% 0.81/0.99  --sup_prop_simpl_given                  true
% 0.81/0.99  --sup_fun_splitting                     false
% 0.81/0.99  --sup_smt_interval                      50000
% 0.81/0.99  
% 0.81/0.99  ------ Superposition Simplification Setup
% 0.81/0.99  
% 0.81/0.99  --sup_indices_passive                   []
% 0.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.99  --sup_full_bw                           [BwDemod]
% 0.81/0.99  --sup_immed_triv                        [TrivRules]
% 0.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.99  --sup_immed_bw_main                     []
% 0.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.81/0.99  
% 0.81/0.99  ------ Combination Options
% 0.81/0.99  
% 0.81/0.99  --comb_res_mult                         3
% 0.81/0.99  --comb_sup_mult                         2
% 0.81/0.99  --comb_inst_mult                        10
% 0.81/0.99  
% 0.81/0.99  ------ Debug Options
% 0.81/0.99  
% 0.81/0.99  --dbg_backtrace                         false
% 0.81/0.99  --dbg_dump_prop_clauses                 false
% 0.81/0.99  --dbg_dump_prop_clauses_file            -
% 0.81/0.99  --dbg_out_stat                          false
% 0.81/0.99  
% 0.81/0.99  
% 0.81/0.99  
% 0.81/0.99  
% 0.81/0.99  ------ Proving...
% 0.81/0.99  
% 0.81/0.99  
% 0.81/0.99  % SZS status Theorem for theBenchmark.p
% 0.81/0.99  
% 0.81/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.81/0.99  
% 0.81/0.99  fof(f5,conjecture,(
% 0.81/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 0.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/0.99  
% 0.81/0.99  fof(f6,negated_conjecture,(
% 0.81/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 0.81/0.99    inference(negated_conjecture,[],[f5])).
% 0.81/0.99  
% 0.81/0.99  fof(f13,plain,(
% 0.81/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X1,X3,X4) & (r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.81/0.99    inference(ennf_transformation,[],[f6])).
% 0.81/0.99  
% 0.81/0.99  fof(f14,plain,(
% 0.81/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 0.81/0.99    inference(flattening,[],[f13])).
% 0.81/0.99  
% 0.81/0.99  fof(f23,plain,(
% 0.81/0.99    ( ! [X4,X2,X5,X3,X1] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,sK6) & sK6 = X4 & X3 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 0.81/0.99    introduced(choice_axiom,[])).
% 0.81/0.99  
% 0.81/0.99  fof(f22,plain,(
% 0.81/0.99    ( ! [X4,X2,X3,X1] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) => (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,sK5,X6) & X4 = X6 & sK5 = X3 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X2)))) )),
% 0.81/0.99    introduced(choice_axiom,[])).
% 0.81/0.99  
% 0.81/0.99  fof(f21,plain,(
% 0.81/0.99    ( ! [X2,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,sK4) & r1_orders_2(X2,X5,X6) & sK4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 0.81/0.99    introduced(choice_axiom,[])).
% 0.81/0.99  
% 0.81/0.99  fof(f20,plain,(
% 0.81/0.99    ( ! [X2,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,sK3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3,u1_struct_0(X1)))) )),
% 0.81/0.99    introduced(choice_axiom,[])).
% 0.81/0.99  
% 0.81/0.99  fof(f19,plain,(
% 0.81/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(sK2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(sK2,X0,X1))) )),
% 0.81/0.99    introduced(choice_axiom,[])).
% 0.81/0.99  
% 0.81/0.99  fof(f18,plain,(
% 0.81/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_yellow_6(X2,X0,sK1)) & l1_waybel_0(sK1,X0))) )),
% 0.81/0.99    introduced(choice_axiom,[])).
% 0.81/0.99  
% 0.81/0.99  fof(f17,plain,(
% 0.81/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,sK0,X1)) & l1_waybel_0(X1,sK0)) & l1_struct_0(sK0))),
% 0.81/0.99    introduced(choice_axiom,[])).
% 0.81/0.99  
% 0.81/0.99  fof(f24,plain,(
% 0.81/0.99    ((((((~r1_orders_2(sK1,sK3,sK4) & r1_orders_2(sK2,sK5,sK6) & sK4 = sK6 & sK3 = sK5 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_yellow_6(sK2,sK0,sK1)) & l1_waybel_0(sK1,sK0)) & l1_struct_0(sK0)),
% 0.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f23,f22,f21,f20,f19,f18,f17])).
% 0.81/0.99  
% 0.81/0.99  fof(f33,plain,(
% 0.81/0.99    m1_yellow_6(sK2,sK0,sK1)),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f2,axiom,(
% 0.81/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/0.99  
% 0.81/0.99  fof(f9,plain,(
% 0.81/0.99    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.81/0.99    inference(ennf_transformation,[],[f2])).
% 0.81/0.99  
% 0.81/0.99  fof(f26,plain,(
% 0.81/0.99    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.81/0.99    inference(cnf_transformation,[],[f9])).
% 0.81/0.99  
% 0.81/0.99  fof(f31,plain,(
% 0.81/0.99    l1_struct_0(sK0)),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f1,axiom,(
% 0.81/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_orders_2(X1,X4,X5) & X3 = X5 & X2 = X4) => r1_orders_2(X0,X2,X3))))))))),
% 0.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/0.99  
% 0.81/0.99  fof(f7,plain,(
% 0.81/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_orders_2(X0,X2,X3) | (~r1_orders_2(X1,X4,X5) | X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.81/0.99    inference(ennf_transformation,[],[f1])).
% 0.81/0.99  
% 0.81/0.99  fof(f8,plain,(
% 0.81/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_orders_2(X0,X2,X3) | ~r1_orders_2(X1,X4,X5) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.81/0.99    inference(flattening,[],[f7])).
% 0.81/0.99  
% 0.81/0.99  fof(f25,plain,(
% 0.81/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_orders_2(X0,X2,X3) | ~r1_orders_2(X1,X4,X5) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.81/0.99    inference(cnf_transformation,[],[f8])).
% 0.81/0.99  
% 0.81/0.99  fof(f42,plain,(
% 0.81/0.99    ( ! [X4,X2,X0,X5,X1] : (r1_orders_2(X0,X2,X5) | ~r1_orders_2(X1,X4,X5) | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.81/0.99    inference(equality_resolution,[],[f25])).
% 0.81/0.99  
% 0.81/0.99  fof(f43,plain,(
% 0.81/0.99    ( ! [X4,X0,X5,X1] : (r1_orders_2(X0,X4,X5) | ~r1_orders_2(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.81/0.99    inference(equality_resolution,[],[f42])).
% 0.81/0.99  
% 0.81/0.99  fof(f3,axiom,(
% 0.81/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 0.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/0.99  
% 0.81/0.99  fof(f10,plain,(
% 0.81/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.81/0.99    inference(ennf_transformation,[],[f3])).
% 0.81/0.99  
% 0.81/0.99  fof(f15,plain,(
% 0.81/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | (u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1))) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.81/0.99    inference(nnf_transformation,[],[f10])).
% 0.81/0.99  
% 0.81/0.99  fof(f16,plain,(
% 0.81/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1)) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.81/0.99    inference(flattening,[],[f15])).
% 0.81/0.99  
% 0.81/0.99  fof(f27,plain,(
% 0.81/0.99    ( ! [X2,X0,X1] : (m1_yellow_0(X2,X1) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.81/0.99    inference(cnf_transformation,[],[f16])).
% 0.81/0.99  
% 0.81/0.99  fof(f4,axiom,(
% 0.81/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 0.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.81/0.99  
% 0.81/0.99  fof(f11,plain,(
% 0.81/0.99    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.81/0.99    inference(ennf_transformation,[],[f4])).
% 0.81/0.99  
% 0.81/0.99  fof(f12,plain,(
% 0.81/0.99    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.81/0.99    inference(flattening,[],[f11])).
% 0.81/0.99  
% 0.81/0.99  fof(f30,plain,(
% 0.81/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.81/0.99    inference(cnf_transformation,[],[f12])).
% 0.81/0.99  
% 0.81/0.99  fof(f32,plain,(
% 0.81/0.99    l1_waybel_0(sK1,sK0)),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f40,plain,(
% 0.81/0.99    r1_orders_2(sK2,sK5,sK6)),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f38,plain,(
% 0.81/0.99    sK3 = sK5),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f39,plain,(
% 0.81/0.99    sK4 = sK6),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f37,plain,(
% 0.81/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f36,plain,(
% 0.81/0.99    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f41,plain,(
% 0.81/0.99    ~r1_orders_2(sK1,sK3,sK4)),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f35,plain,(
% 0.81/0.99    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  fof(f34,plain,(
% 0.81/0.99    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.81/0.99    inference(cnf_transformation,[],[f24])).
% 0.81/0.99  
% 0.81/0.99  cnf(c_14,negated_conjecture,
% 0.81/0.99      ( m1_yellow_6(sK2,sK0,sK1) ),
% 0.81/0.99      inference(cnf_transformation,[],[f33]) ).
% 0.81/0.99  
% 0.81/0.99  cnf(c_1,plain,
% 0.81/0.99      ( ~ l1_waybel_0(X0,X1) | ~ l1_struct_0(X1) | l1_orders_2(X0) ),
% 0.81/0.99      inference(cnf_transformation,[],[f26]) ).
% 0.81/0.99  
% 0.81/0.99  cnf(c_16,negated_conjecture,
% 0.81/0.99      ( l1_struct_0(sK0) ),
% 0.81/0.99      inference(cnf_transformation,[],[f31]) ).
% 0.81/0.99  
% 0.81/0.99  cnf(c_267,plain,
% 0.81/1.00      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | sK0 != X1 ),
% 0.81/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_268,plain,
% 0.81/1.00      ( ~ l1_waybel_0(X0,sK0) | l1_orders_2(X0) ),
% 0.81/1.00      inference(unflattening,[status(thm)],[c_267]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_0,plain,
% 0.81/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 0.81/1.00      | r1_orders_2(X3,X1,X2)
% 0.81/1.00      | ~ m1_yellow_0(X0,X3)
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(X3))
% 0.81/1.00      | ~ l1_orders_2(X3) ),
% 0.81/1.00      inference(cnf_transformation,[],[f43]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_300,plain,
% 0.81/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 0.81/1.00      | r1_orders_2(X3,X1,X2)
% 0.81/1.00      | ~ l1_waybel_0(X4,sK0)
% 0.81/1.00      | ~ m1_yellow_0(X0,X3)
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(X3))
% 0.81/1.00      | X3 != X4 ),
% 0.81/1.00      inference(resolution_lifted,[status(thm)],[c_268,c_0]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_301,plain,
% 0.81/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 0.81/1.00      | r1_orders_2(X3,X1,X2)
% 0.81/1.00      | ~ l1_waybel_0(X3,sK0)
% 0.81/1.00      | ~ m1_yellow_0(X0,X3)
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(X3)) ),
% 0.81/1.00      inference(unflattening,[status(thm)],[c_300]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_4,plain,
% 0.81/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 0.81/1.00      | ~ l1_waybel_0(X2,X1)
% 0.81/1.00      | ~ l1_waybel_0(X0,X1)
% 0.81/1.00      | m1_yellow_0(X0,X2)
% 0.81/1.00      | ~ l1_struct_0(X1) ),
% 0.81/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_5,plain,
% 0.81/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 0.81/1.00      | ~ l1_waybel_0(X2,X1)
% 0.81/1.00      | l1_waybel_0(X0,X1)
% 0.81/1.00      | ~ l1_struct_0(X1) ),
% 0.81/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_81,plain,
% 0.81/1.00      ( ~ l1_waybel_0(X2,X1)
% 0.81/1.00      | ~ m1_yellow_6(X0,X1,X2)
% 0.81/1.00      | m1_yellow_0(X0,X2)
% 0.81/1.00      | ~ l1_struct_0(X1) ),
% 0.81/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4,c_5]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_82,plain,
% 0.81/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 0.81/1.00      | ~ l1_waybel_0(X2,X1)
% 0.81/1.00      | m1_yellow_0(X0,X2)
% 0.81/1.00      | ~ l1_struct_0(X1) ),
% 0.81/1.00      inference(renaming,[status(thm)],[c_81]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_218,plain,
% 0.81/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 0.81/1.00      | ~ l1_waybel_0(X2,X1)
% 0.81/1.00      | m1_yellow_0(X0,X2)
% 0.81/1.00      | sK0 != X1 ),
% 0.81/1.00      inference(resolution_lifted,[status(thm)],[c_82,c_16]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_219,plain,
% 0.81/1.00      ( ~ m1_yellow_6(X0,sK0,X1)
% 0.81/1.00      | ~ l1_waybel_0(X1,sK0)
% 0.81/1.00      | m1_yellow_0(X0,X1) ),
% 0.81/1.00      inference(unflattening,[status(thm)],[c_218]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_338,plain,
% 0.81/1.00      ( ~ m1_yellow_6(X0,sK0,X1)
% 0.81/1.00      | ~ r1_orders_2(X2,X3,X4)
% 0.81/1.00      | r1_orders_2(X5,X3,X4)
% 0.81/1.00      | ~ l1_waybel_0(X5,sK0)
% 0.81/1.00      | ~ l1_waybel_0(X1,sK0)
% 0.81/1.00      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 0.81/1.00      | ~ m1_subset_1(X3,u1_struct_0(X5))
% 0.81/1.00      | ~ m1_subset_1(X4,u1_struct_0(X2))
% 0.81/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 0.81/1.00      | X1 != X5
% 0.81/1.00      | X0 != X2 ),
% 0.81/1.00      inference(resolution_lifted,[status(thm)],[c_301,c_219]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_339,plain,
% 0.81/1.00      ( ~ m1_yellow_6(X0,sK0,X1)
% 0.81/1.00      | ~ r1_orders_2(X0,X2,X3)
% 0.81/1.00      | r1_orders_2(X1,X2,X3)
% 0.81/1.00      | ~ l1_waybel_0(X1,sK0)
% 0.81/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
% 0.81/1.00      inference(unflattening,[status(thm)],[c_338]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_375,plain,
% 0.81/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 0.81/1.00      | r1_orders_2(X3,X1,X2)
% 0.81/1.00      | ~ l1_waybel_0(X3,sK0)
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 0.81/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(X3))
% 0.81/1.00      | sK0 != sK0
% 0.81/1.00      | sK2 != X0
% 0.81/1.00      | sK1 != X3 ),
% 0.81/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_339]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_376,plain,
% 0.81/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 0.81/1.00      | r1_orders_2(sK1,X0,X1)
% 0.81/1.00      | ~ l1_waybel_0(sK1,sK0)
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 0.81/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_15,negated_conjecture,
% 0.81/1.00      ( l1_waybel_0(sK1,sK0) ),
% 0.81/1.00      inference(cnf_transformation,[],[f32]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_380,plain,
% 0.81/1.00      ( r1_orders_2(sK1,X0,X1)
% 0.81/1.00      | ~ r1_orders_2(sK2,X0,X1)
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 0.81/1.00      inference(global_propositional_subsumption,
% 0.81/1.00                [status(thm)],
% 0.81/1.00                [c_376,c_15]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_381,plain,
% 0.81/1.00      ( ~ r1_orders_2(sK2,X0,X1)
% 0.81/1.00      | r1_orders_2(sK1,X0,X1)
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.81/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 0.81/1.00      inference(renaming,[status(thm)],[c_380]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_485,plain,
% 0.81/1.00      ( ~ r1_orders_2(sK2,X0_48,X1_48)
% 0.81/1.00      | r1_orders_2(sK1,X0_48,X1_48)
% 0.81/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X1_48,u1_struct_0(sK1))
% 0.81/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK1)) ),
% 0.81/1.00      inference(subtyping,[status(esa)],[c_381]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_740,plain,
% 0.81/1.00      ( ~ r1_orders_2(sK2,X0_48,sK4)
% 0.81/1.00      | r1_orders_2(sK1,X0_48,sK4)
% 0.81/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(X0_48,u1_struct_0(sK1))
% 0.81/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 0.81/1.00      inference(instantiation,[status(thm)],[c_485]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_742,plain,
% 0.81/1.00      ( ~ r1_orders_2(sK2,sK3,sK4)
% 0.81/1.00      | r1_orders_2(sK1,sK3,sK4)
% 0.81/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 0.81/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 0.81/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 0.81/1.00      inference(instantiation,[status(thm)],[c_740]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_7,negated_conjecture,
% 0.81/1.00      ( r1_orders_2(sK2,sK5,sK6) ),
% 0.81/1.00      inference(cnf_transformation,[],[f40]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_492,negated_conjecture,
% 0.81/1.00      ( r1_orders_2(sK2,sK5,sK6) ),
% 0.81/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_635,plain,
% 0.81/1.00      ( r1_orders_2(sK2,sK5,sK6) = iProver_top ),
% 0.81/1.00      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_9,negated_conjecture,
% 0.81/1.00      ( sK3 = sK5 ),
% 0.81/1.00      inference(cnf_transformation,[],[f38]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_490,negated_conjecture,
% 0.81/1.00      ( sK3 = sK5 ),
% 0.81/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_8,negated_conjecture,
% 0.81/1.00      ( sK4 = sK6 ),
% 0.81/1.00      inference(cnf_transformation,[],[f39]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_491,negated_conjecture,
% 0.81/1.00      ( sK4 = sK6 ),
% 0.81/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_645,plain,
% 0.81/1.00      ( r1_orders_2(sK2,sK3,sK4) = iProver_top ),
% 0.81/1.00      inference(light_normalisation,[status(thm)],[c_635,c_490,c_491]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_680,plain,
% 0.81/1.00      ( r1_orders_2(sK2,sK3,sK4) ),
% 0.81/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_645]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_10,negated_conjecture,
% 0.81/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 0.81/1.00      inference(cnf_transformation,[],[f37]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_489,negated_conjecture,
% 0.81/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 0.81/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_636,plain,
% 0.81/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 0.81/1.00      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_648,plain,
% 0.81/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 0.81/1.00      inference(light_normalisation,[status(thm)],[c_636,c_491]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_679,plain,
% 0.81/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 0.81/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_648]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_11,negated_conjecture,
% 0.81/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.81/1.00      inference(cnf_transformation,[],[f36]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_488,negated_conjecture,
% 0.81/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.81/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_637,plain,
% 0.81/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 0.81/1.00      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_651,plain,
% 0.81/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 0.81/1.00      inference(light_normalisation,[status(thm)],[c_637,c_490]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_674,plain,
% 0.81/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 0.81/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_651]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_6,negated_conjecture,
% 0.81/1.00      ( ~ r1_orders_2(sK1,sK3,sK4) ),
% 0.81/1.00      inference(cnf_transformation,[],[f41]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_12,negated_conjecture,
% 0.81/1.00      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 0.81/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(c_13,negated_conjecture,
% 0.81/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 0.81/1.00      inference(cnf_transformation,[],[f34]) ).
% 0.81/1.00  
% 0.81/1.00  cnf(contradiction,plain,
% 0.81/1.00      ( $false ),
% 0.81/1.00      inference(minisat,
% 0.81/1.00                [status(thm)],
% 0.81/1.00                [c_742,c_680,c_679,c_674,c_6,c_12,c_13]) ).
% 0.81/1.00  
% 0.81/1.00  
% 0.81/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.81/1.00  
% 0.81/1.00  ------                               Statistics
% 0.81/1.00  
% 0.81/1.00  ------ General
% 0.81/1.00  
% 0.81/1.00  abstr_ref_over_cycles:                  0
% 0.81/1.00  abstr_ref_under_cycles:                 0
% 0.81/1.00  gc_basic_clause_elim:                   0
% 0.81/1.00  forced_gc_time:                         0
% 0.81/1.00  parsing_time:                           0.01
% 0.81/1.00  unif_index_cands_time:                  0.
% 0.81/1.00  unif_index_add_time:                    0.
% 0.81/1.00  orderings_time:                         0.
% 0.81/1.00  out_proof_time:                         0.01
% 0.81/1.00  total_time:                             0.057
% 0.81/1.00  num_of_symbols:                         49
% 0.81/1.00  num_of_terms:                           713
% 0.81/1.00  
% 0.81/1.00  ------ Preprocessing
% 0.81/1.00  
% 0.81/1.00  num_of_splits:                          0
% 0.81/1.00  num_of_split_atoms:                     0
% 0.81/1.00  num_of_reused_defs:                     0
% 0.81/1.00  num_eq_ax_congr_red:                    13
% 0.81/1.00  num_of_sem_filtered_clauses:            5
% 0.81/1.00  num_of_subtypes:                        4
% 0.81/1.00  monotx_restored_types:                  0
% 0.81/1.00  sat_num_of_epr_types:                   0
% 0.81/1.00  sat_num_of_non_cyclic_types:            0
% 0.81/1.00  sat_guarded_non_collapsed_types:        0
% 0.81/1.00  num_pure_diseq_elim:                    0
% 0.81/1.00  simp_replaced_by:                       0
% 0.81/1.00  res_preprocessed:                       58
% 0.81/1.00  prep_upred:                             0
% 0.81/1.00  prep_unflattend:                        15
% 0.81/1.00  smt_new_axioms:                         0
% 0.81/1.00  pred_elim_cands:                        2
% 0.81/1.00  pred_elim:                              5
% 0.81/1.00  pred_elim_cl:                           7
% 0.81/1.00  pred_elim_cycles:                       8
% 0.81/1.00  merged_defs:                            0
% 0.81/1.00  merged_defs_ncl:                        0
% 0.81/1.00  bin_hyper_res:                          0
% 0.81/1.00  prep_cycles:                            4
% 0.81/1.00  pred_elim_time:                         0.005
% 0.81/1.00  splitting_time:                         0.
% 0.81/1.00  sem_filter_time:                        0.
% 0.81/1.00  monotx_time:                            0.
% 0.81/1.00  subtype_inf_time:                       0.
% 0.81/1.00  
% 0.81/1.00  ------ Problem properties
% 0.81/1.00  
% 0.81/1.00  clauses:                                10
% 0.81/1.00  conjectures:                            8
% 0.81/1.00  epr:                                    4
% 0.81/1.00  horn:                                   10
% 0.81/1.00  ground:                                 9
% 0.81/1.00  unary:                                  9
% 0.81/1.00  binary:                                 0
% 0.81/1.00  lits:                                   15
% 0.81/1.00  lits_eq:                                3
% 0.81/1.00  fd_pure:                                0
% 0.81/1.00  fd_pseudo:                              0
% 0.81/1.00  fd_cond:                                0
% 0.81/1.00  fd_pseudo_cond:                         0
% 0.81/1.00  ac_symbols:                             0
% 0.81/1.00  
% 0.81/1.00  ------ Propositional Solver
% 0.81/1.00  
% 0.81/1.00  prop_solver_calls:                      23
% 0.81/1.00  prop_fast_solver_calls:                 300
% 0.81/1.00  smt_solver_calls:                       0
% 0.81/1.00  smt_fast_solver_calls:                  0
% 0.81/1.00  prop_num_of_clauses:                    142
% 0.81/1.00  prop_preprocess_simplified:             1090
% 0.81/1.00  prop_fo_subsumed:                       5
% 0.81/1.00  prop_solver_time:                       0.
% 0.81/1.00  smt_solver_time:                        0.
% 0.81/1.00  smt_fast_solver_time:                   0.
% 0.81/1.00  prop_fast_solver_time:                  0.
% 0.81/1.00  prop_unsat_core_time:                   0.
% 0.81/1.00  
% 0.81/1.00  ------ QBF
% 0.81/1.00  
% 0.81/1.00  qbf_q_res:                              0
% 0.81/1.00  qbf_num_tautologies:                    0
% 0.81/1.00  qbf_prep_cycles:                        0
% 0.81/1.00  
% 0.81/1.00  ------ BMC1
% 0.81/1.00  
% 0.81/1.00  bmc1_current_bound:                     -1
% 0.81/1.00  bmc1_last_solved_bound:                 -1
% 0.81/1.00  bmc1_unsat_core_size:                   -1
% 0.81/1.00  bmc1_unsat_core_parents_size:           -1
% 0.81/1.00  bmc1_merge_next_fun:                    0
% 0.81/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.81/1.00  
% 0.81/1.00  ------ Instantiation
% 0.81/1.00  
% 0.81/1.00  inst_num_of_clauses:                    26
% 0.81/1.00  inst_num_in_passive:                    6
% 0.81/1.00  inst_num_in_active:                     19
% 0.81/1.00  inst_num_in_unprocessed:                0
% 0.81/1.00  inst_num_of_loops:                      22
% 0.81/1.00  inst_num_of_learning_restarts:          0
% 0.81/1.00  inst_num_moves_active_passive:          0
% 0.81/1.00  inst_lit_activity:                      0
% 0.81/1.00  inst_lit_activity_moves:                0
% 0.81/1.00  inst_num_tautologies:                   0
% 0.81/1.00  inst_num_prop_implied:                  0
% 0.81/1.00  inst_num_existing_simplified:           0
% 0.81/1.00  inst_num_eq_res_simplified:             0
% 0.81/1.00  inst_num_child_elim:                    0
% 0.81/1.00  inst_num_of_dismatching_blockings:      0
% 0.81/1.00  inst_num_of_non_proper_insts:           14
% 0.81/1.00  inst_num_of_duplicates:                 0
% 0.81/1.00  inst_inst_num_from_inst_to_res:         0
% 0.81/1.00  inst_dismatching_checking_time:         0.
% 0.81/1.00  
% 0.81/1.00  ------ Resolution
% 0.81/1.00  
% 0.81/1.00  res_num_of_clauses:                     0
% 0.81/1.00  res_num_in_passive:                     0
% 0.81/1.00  res_num_in_active:                      0
% 0.81/1.00  res_num_of_loops:                       62
% 0.81/1.00  res_forward_subset_subsumed:            0
% 0.81/1.00  res_backward_subset_subsumed:           0
% 0.81/1.00  res_forward_subsumed:                   0
% 0.81/1.00  res_backward_subsumed:                  0
% 0.81/1.00  res_forward_subsumption_resolution:     0
% 0.81/1.00  res_backward_subsumption_resolution:    0
% 0.81/1.00  res_clause_to_clause_subsumption:       10
% 0.81/1.00  res_orphan_elimination:                 0
% 0.81/1.00  res_tautology_del:                      1
% 0.81/1.00  res_num_eq_res_simplified:              0
% 0.81/1.00  res_num_sel_changes:                    0
% 0.81/1.00  res_moves_from_active_to_pass:          0
% 0.81/1.00  
% 0.81/1.00  ------ Superposition
% 0.81/1.00  
% 0.81/1.00  sup_time_total:                         0.
% 0.81/1.00  sup_time_generating:                    0.
% 0.81/1.00  sup_time_sim_full:                      0.
% 0.81/1.00  sup_time_sim_immed:                     0.
% 0.81/1.00  
% 0.81/1.00  sup_num_of_clauses:                     10
% 0.81/1.00  sup_num_in_active:                      4
% 0.81/1.00  sup_num_in_passive:                     6
% 0.81/1.00  sup_num_of_loops:                       4
% 0.81/1.00  sup_fw_superposition:                   0
% 0.81/1.00  sup_bw_superposition:                   0
% 0.81/1.00  sup_immediate_simplified:               0
% 0.81/1.00  sup_given_eliminated:                   0
% 0.81/1.00  comparisons_done:                       0
% 0.81/1.00  comparisons_avoided:                    0
% 0.81/1.00  
% 0.81/1.00  ------ Simplifications
% 0.81/1.00  
% 0.81/1.00  
% 0.81/1.00  sim_fw_subset_subsumed:                 0
% 0.81/1.00  sim_bw_subset_subsumed:                 0
% 0.81/1.00  sim_fw_subsumed:                        0
% 0.81/1.00  sim_bw_subsumed:                        0
% 0.81/1.00  sim_fw_subsumption_res:                 0
% 0.81/1.00  sim_bw_subsumption_res:                 0
% 0.81/1.00  sim_tautology_del:                      0
% 0.81/1.00  sim_eq_tautology_del:                   0
% 0.81/1.00  sim_eq_res_simp:                        0
% 0.81/1.00  sim_fw_demodulated:                     0
% 0.81/1.00  sim_bw_demodulated:                     0
% 0.81/1.00  sim_light_normalised:                   3
% 0.81/1.00  sim_joinable_taut:                      0
% 0.81/1.00  sim_joinable_simp:                      0
% 0.81/1.00  sim_ac_normalised:                      0
% 0.81/1.00  sim_smt_subsumption:                    0
% 0.81/1.00  
%------------------------------------------------------------------------------
