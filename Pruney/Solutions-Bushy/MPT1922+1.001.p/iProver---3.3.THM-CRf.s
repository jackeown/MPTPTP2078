%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1922+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:53 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 251 expanded)
%              Number of clauses        :   46 (  51 expanded)
%              Number of leaves         :   12 ( 116 expanded)
%              Depth                    :   20
%              Number of atoms          :  440 (2619 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f12])).

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
    inference(equality_resolution,[],[f30])).

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

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( l1_waybel_0(X2,X0)
             => ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f7])).

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

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

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

cnf(c_3,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_246,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_247,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_246])).

cnf(c_5,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_yellow_0(X0,X3)
    | ~ l1_orders_2(X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_300,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X4,sK0)
    | ~ m1_yellow_0(X0,X3)
    | X3 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_247,c_5])).

cnf(c_301,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,sK0)
    | ~ m1_yellow_0(X0,X3) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_2,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_83,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_4])).

cnf(c_218,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_83,c_16])).

cnf(c_219,plain,
    ( ~ m1_yellow_6(X0,sK0,X1)
    | ~ l1_waybel_0(X1,sK0)
    | m1_yellow_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_338,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_yellow_6(X4,sK0,X5)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,sK0)
    | ~ l1_waybel_0(X5,sK0)
    | X5 != X3
    | X4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_301,c_219])).

cnf(c_339,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_yellow_6(X0,sK0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,sK0) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_394,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,sK0)
    | sK0 != sK0
    | sK2 != X0
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_339])).

cnf(c_395,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_15,negated_conjecture,
    ( l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_orders_2(sK1,X0,X1)
    | ~ r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_15])).

cnf(c_400,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r1_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_399])).

cnf(c_484,plain,
    ( ~ r1_orders_2(sK2,X0_46,X1_46)
    | r1_orders_2(sK1,X0_46,X1_46)
    | ~ m1_subset_1(X1_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_46,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_400])).

cnf(c_740,plain,
    ( ~ r1_orders_2(sK2,X0_46,sK4)
    | r1_orders_2(sK1,X0_46,sK4)
    | ~ m1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_46,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_484])).

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
