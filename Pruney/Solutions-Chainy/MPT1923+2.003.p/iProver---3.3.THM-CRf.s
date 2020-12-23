%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:06 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 833 expanded)
%              Number of clauses        :   84 ( 184 expanded)
%              Number of leaves         :   16 ( 366 expanded)
%              Depth                    :   24
%              Number of atoms          :  606 (9148 expanded)
%              Number of equality atoms :  133 (1759 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
                & v2_yellow_6(X2,X0,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X1,X3,X4)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_yellow_6(X2,X0,X1)
                  & v2_yellow_6(X2,X0,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X1,X3,X4)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X2,X5,X6)
          & r1_orders_2(X1,X3,X4)
          & X4 = X6
          & X3 = X5
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X2,X5,sK6)
        & r1_orders_2(X1,X3,X4)
        & sK6 = X4
        & X3 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X4,X2,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(X2,X5,X6)
              & r1_orders_2(X1,X3,X4)
              & X4 = X6
              & X3 = X5
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( ? [X6] :
            ( ~ r1_orders_2(X2,sK5,X6)
            & r1_orders_2(X1,X3,X4)
            & X4 = X6
            & sK5 = X3
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(X2,X5,X6)
                  & r1_orders_2(X1,X3,X4)
                  & X4 = X6
                  & X3 = X5
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X2)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(X2,X5,X6)
                & r1_orders_2(X1,X3,sK4)
                & sK4 = X6
                & X3 = X5
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(X2,X5,X6)
                      & r1_orders_2(X1,X3,X4)
                      & X4 = X6
                      & X3 = X5
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X2)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(X2,X5,X6)
                    & r1_orders_2(X1,sK3,X4)
                    & X4 = X6
                    & sK3 = X5
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_orders_2(X2,X5,X6)
                          & r1_orders_2(X1,X3,X4)
                          & X4 = X6
                          & X3 = X5
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & m1_yellow_6(X2,X0,X1)
          & v2_yellow_6(X2,X0,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(sK2,X5,X6)
                        & r1_orders_2(X1,X3,X4)
                        & X4 = X6
                        & X3 = X5
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(sK2)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_yellow_6(sK2,X0,X1)
        & v2_yellow_6(sK2,X0,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_orders_2(X2,X5,X6)
                            & r1_orders_2(sK1,X3,X4)
                            & X4 = X6
                            & X3 = X5
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            & m1_yellow_6(X2,X0,sK1)
            & v2_yellow_6(X2,X0,sK1)
            & ~ v2_struct_0(X2) )
        & l1_waybel_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_orders_2(X2,X5,X6)
                                & r1_orders_2(X1,X3,X4)
                                & X4 = X6
                                & X3 = X5
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_yellow_6(X2,X0,X1)
                & v2_yellow_6(X2,X0,X1)
                & ~ v2_struct_0(X2) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,sK0,X1)
              & v2_yellow_6(X2,sK0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_orders_2(sK2,sK5,sK6)
    & r1_orders_2(sK1,sK3,sK4)
    & sK4 = sK6
    & sK3 = sK5
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_yellow_6(sK2,sK0,sK1)
    & v2_yellow_6(sK2,sK0,sK1)
    & ~ v2_struct_0(sK2)
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f24,f33,f32,f31,f30,f29,f28,f27])).

fof(f52,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f60,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_yellow_6(X2,X0,X1)
                  | ~ m1_yellow_0(X2,X1)
                  | ~ v4_yellow_0(X2,X1) )
                & ( ( m1_yellow_0(X2,X1)
                    & v4_yellow_0(X2,X1) )
                  | ~ v2_yellow_6(X2,X0,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ v2_yellow_6(X2,X0,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    v2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v4_yellow_0(X2,X1)
      | ~ v2_yellow_6(X2,X0,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ~ r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_741,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_941,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_409,plain,
    ( l1_orders_2(X0)
    | ~ l1_struct_0(X1)
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_410,plain,
    ( l1_orders_2(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_412,plain,
    ( l1_orders_2(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_23])).

cnf(c_476,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_412])).

cnf(c_477,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_507,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_477])).

cnf(c_508,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_735,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_508])).

cnf(c_12,negated_conjecture,
    ( sK4 = sK6 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_745,negated_conjecture,
    ( sK4 = sK6 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_965,plain,
    ( m1_subset_1(sK6,k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_941,c_735,c_745])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_740,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_942,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_13,negated_conjecture,
    ( sK3 = sK5 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_744,negated_conjecture,
    ( sK3 = sK5 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_968,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_942,c_735,c_744])).

cnf(c_4,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ v4_yellow_0(X3,X0)
    | ~ m1_yellow_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ v2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,negated_conjecture,
    ( m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_390,plain,
    ( ~ v2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1)
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_391,plain,
    ( ~ v2_yellow_6(sK2,sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_19,negated_conjecture,
    ( v2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_393,plain,
    ( m1_yellow_0(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_23,c_21,c_19])).

cnf(c_435,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ v4_yellow_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X0)
    | sK1 != X0
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_393])).

cnf(c_436,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r1_orders_2(sK2,X0,X1)
    | ~ v4_yellow_0(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_8,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ v2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v4_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_379,plain,
    ( ~ v2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v4_yellow_0(X0,X2)
    | ~ l1_struct_0(X1)
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_380,plain,
    ( ~ v2_yellow_6(sK2,sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v4_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,X0,X1)
    | r1_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_23,c_21,c_19,c_380,c_410])).

cnf(c_441,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_739,plain,
    ( ~ r1_orders_2(sK1,X0_51,X1_51)
    | r1_orders_2(sK2,X0_51,X1_51)
    | ~ m1_subset_1(X1_51,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK2))
    | ~ r2_hidden(X0_51,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_441])).

cnf(c_943,plain,
    ( r1_orders_2(sK1,X0_51,X1_51) != iProver_top
    | r1_orders_2(sK2,X0_51,X1_51) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_51,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_9,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_368,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | sK0 != X1
    | sK1 != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_369,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | l1_waybel_0(sK2,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_371,plain,
    ( l1_waybel_0(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_23,c_21])).

cnf(c_420,plain,
    ( l1_orders_2(X0)
    | ~ l1_struct_0(X1)
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_371])).

cnf(c_421,plain,
    ( l1_orders_2(sK2)
    | ~ l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_423,plain,
    ( l1_orders_2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_23])).

cnf(c_483,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_423])).

cnf(c_484,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_512,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_484])).

cnf(c_513,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_734,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_981,plain,
    ( r1_orders_2(sK1,X0_51,X1_51) != iProver_top
    | r1_orders_2(sK2,X0_51,X1_51) = iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_51,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_51,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_51,k2_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_943,c_734,c_735])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_253,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_254,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(k2_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | ~ l1_struct_0(sK2)
    | k2_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_254])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k2_struct_0(sK2))
    | r2_hidden(X0,k2_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k2_struct_0(sK2))
    | r2_hidden(X0,k2_struct_0(sK2)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_484,c_295])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0_51,k2_struct_0(sK2))
    | r2_hidden(X0_51,k2_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_497])).

cnf(c_945,plain,
    ( m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_51,k2_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_989,plain,
    ( r1_orders_2(sK1,X0_51,X1_51) != iProver_top
    | r1_orders_2(sK2,X0_51,X1_51) = iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_51,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_51,k2_struct_0(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_981,c_945])).

cnf(c_1439,plain,
    ( r1_orders_2(sK1,sK5,X0_51) != iProver_top
    | r1_orders_2(sK2,sK5,X0_51) = iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_968,c_989])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_742,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_940,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_962,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_940,c_734])).

cnf(c_1613,plain,
    ( m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
    | r1_orders_2(sK2,sK5,X0_51) = iProver_top
    | r1_orders_2(sK1,sK5,X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1439,c_962])).

cnf(c_1614,plain,
    ( r1_orders_2(sK1,sK5,X0_51) != iProver_top
    | r1_orders_2(sK2,sK5,X0_51) = iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1613])).

cnf(c_1623,plain,
    ( r1_orders_2(sK1,sK5,sK6) != iProver_top
    | r1_orders_2(sK2,sK5,sK6) = iProver_top
    | m1_subset_1(sK6,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_965,c_1614])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_743,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_939,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_959,plain,
    ( m1_subset_1(sK6,k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_939,c_734])).

cnf(c_11,negated_conjecture,
    ( r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_746,negated_conjecture,
    ( r1_orders_2(sK1,sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_938,plain,
    ( r1_orders_2(sK1,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_956,plain,
    ( r1_orders_2(sK1,sK5,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_938,c_744,c_745])).

cnf(c_10,negated_conjecture,
    ( ~ r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_35,plain,
    ( r1_orders_2(sK2,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1623,c_959,c_956,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:53:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.98/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.98/0.99  
% 0.98/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.98/0.99  
% 0.98/0.99  ------  iProver source info
% 0.98/0.99  
% 0.98/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.98/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.98/0.99  git: non_committed_changes: false
% 0.98/0.99  git: last_make_outside_of_git: false
% 0.98/0.99  
% 0.98/0.99  ------ 
% 0.98/0.99  
% 0.98/0.99  ------ Input Options
% 0.98/0.99  
% 0.98/0.99  --out_options                           all
% 0.98/0.99  --tptp_safe_out                         true
% 0.98/0.99  --problem_path                          ""
% 0.98/0.99  --include_path                          ""
% 0.98/0.99  --clausifier                            res/vclausify_rel
% 0.98/0.99  --clausifier_options                    --mode clausify
% 0.98/0.99  --stdin                                 false
% 0.98/0.99  --stats_out                             all
% 0.98/0.99  
% 0.98/0.99  ------ General Options
% 0.98/0.99  
% 0.98/0.99  --fof                                   false
% 0.98/0.99  --time_out_real                         305.
% 0.98/0.99  --time_out_virtual                      -1.
% 0.98/0.99  --symbol_type_check                     false
% 0.98/0.99  --clausify_out                          false
% 0.98/0.99  --sig_cnt_out                           false
% 0.98/0.99  --trig_cnt_out                          false
% 0.98/0.99  --trig_cnt_out_tolerance                1.
% 0.98/0.99  --trig_cnt_out_sk_spl                   false
% 0.98/0.99  --abstr_cl_out                          false
% 0.98/0.99  
% 0.98/0.99  ------ Global Options
% 0.98/0.99  
% 0.98/0.99  --schedule                              default
% 0.98/0.99  --add_important_lit                     false
% 0.98/0.99  --prop_solver_per_cl                    1000
% 0.98/0.99  --min_unsat_core                        false
% 0.98/0.99  --soft_assumptions                      false
% 0.98/0.99  --soft_lemma_size                       3
% 0.98/0.99  --prop_impl_unit_size                   0
% 0.98/0.99  --prop_impl_unit                        []
% 0.98/0.99  --share_sel_clauses                     true
% 0.98/0.99  --reset_solvers                         false
% 0.98/0.99  --bc_imp_inh                            [conj_cone]
% 0.98/0.99  --conj_cone_tolerance                   3.
% 0.98/0.99  --extra_neg_conj                        none
% 0.98/0.99  --large_theory_mode                     true
% 0.98/0.99  --prolific_symb_bound                   200
% 0.98/0.99  --lt_threshold                          2000
% 0.98/0.99  --clause_weak_htbl                      true
% 0.98/0.99  --gc_record_bc_elim                     false
% 0.98/0.99  
% 0.98/0.99  ------ Preprocessing Options
% 0.98/0.99  
% 0.98/0.99  --preprocessing_flag                    true
% 0.98/0.99  --time_out_prep_mult                    0.1
% 0.98/0.99  --splitting_mode                        input
% 0.98/0.99  --splitting_grd                         true
% 0.98/0.99  --splitting_cvd                         false
% 0.98/0.99  --splitting_cvd_svl                     false
% 0.98/0.99  --splitting_nvd                         32
% 0.98/0.99  --sub_typing                            true
% 0.98/0.99  --prep_gs_sim                           true
% 0.98/0.99  --prep_unflatten                        true
% 0.98/0.99  --prep_res_sim                          true
% 0.98/0.99  --prep_upred                            true
% 0.98/0.99  --prep_sem_filter                       exhaustive
% 0.98/0.99  --prep_sem_filter_out                   false
% 0.98/0.99  --pred_elim                             true
% 0.98/0.99  --res_sim_input                         true
% 0.98/0.99  --eq_ax_congr_red                       true
% 0.98/0.99  --pure_diseq_elim                       true
% 0.98/0.99  --brand_transform                       false
% 0.98/0.99  --non_eq_to_eq                          false
% 0.98/0.99  --prep_def_merge                        true
% 0.98/0.99  --prep_def_merge_prop_impl              false
% 0.98/0.99  --prep_def_merge_mbd                    true
% 0.98/0.99  --prep_def_merge_tr_red                 false
% 0.98/0.99  --prep_def_merge_tr_cl                  false
% 0.98/0.99  --smt_preprocessing                     true
% 0.98/0.99  --smt_ac_axioms                         fast
% 0.98/0.99  --preprocessed_out                      false
% 0.98/0.99  --preprocessed_stats                    false
% 0.98/0.99  
% 0.98/0.99  ------ Abstraction refinement Options
% 0.98/0.99  
% 0.98/0.99  --abstr_ref                             []
% 0.98/0.99  --abstr_ref_prep                        false
% 0.98/0.99  --abstr_ref_until_sat                   false
% 0.98/0.99  --abstr_ref_sig_restrict                funpre
% 0.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/0.99  --abstr_ref_under                       []
% 0.98/0.99  
% 0.98/0.99  ------ SAT Options
% 0.98/0.99  
% 0.98/0.99  --sat_mode                              false
% 0.98/0.99  --sat_fm_restart_options                ""
% 0.98/0.99  --sat_gr_def                            false
% 0.98/0.99  --sat_epr_types                         true
% 0.98/0.99  --sat_non_cyclic_types                  false
% 0.98/0.99  --sat_finite_models                     false
% 0.98/0.99  --sat_fm_lemmas                         false
% 0.98/0.99  --sat_fm_prep                           false
% 0.98/0.99  --sat_fm_uc_incr                        true
% 0.98/0.99  --sat_out_model                         small
% 0.98/0.99  --sat_out_clauses                       false
% 0.98/0.99  
% 0.98/0.99  ------ QBF Options
% 0.98/0.99  
% 0.98/0.99  --qbf_mode                              false
% 0.98/0.99  --qbf_elim_univ                         false
% 0.98/0.99  --qbf_dom_inst                          none
% 0.98/0.99  --qbf_dom_pre_inst                      false
% 0.98/0.99  --qbf_sk_in                             false
% 0.98/0.99  --qbf_pred_elim                         true
% 0.98/0.99  --qbf_split                             512
% 0.98/0.99  
% 0.98/0.99  ------ BMC1 Options
% 0.98/0.99  
% 0.98/0.99  --bmc1_incremental                      false
% 0.98/0.99  --bmc1_axioms                           reachable_all
% 0.98/0.99  --bmc1_min_bound                        0
% 0.98/0.99  --bmc1_max_bound                        -1
% 0.98/0.99  --bmc1_max_bound_default                -1
% 0.98/0.99  --bmc1_symbol_reachability              true
% 0.98/0.99  --bmc1_property_lemmas                  false
% 0.98/0.99  --bmc1_k_induction                      false
% 0.98/0.99  --bmc1_non_equiv_states                 false
% 0.98/0.99  --bmc1_deadlock                         false
% 0.98/0.99  --bmc1_ucm                              false
% 0.98/0.99  --bmc1_add_unsat_core                   none
% 0.98/0.99  --bmc1_unsat_core_children              false
% 0.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/0.99  --bmc1_out_stat                         full
% 0.98/0.99  --bmc1_ground_init                      false
% 0.98/0.99  --bmc1_pre_inst_next_state              false
% 0.98/0.99  --bmc1_pre_inst_state                   false
% 0.98/0.99  --bmc1_pre_inst_reach_state             false
% 0.98/0.99  --bmc1_out_unsat_core                   false
% 0.98/0.99  --bmc1_aig_witness_out                  false
% 0.98/0.99  --bmc1_verbose                          false
% 0.98/0.99  --bmc1_dump_clauses_tptp                false
% 0.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.98/0.99  --bmc1_dump_file                        -
% 0.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.98/0.99  --bmc1_ucm_extend_mode                  1
% 0.98/0.99  --bmc1_ucm_init_mode                    2
% 0.98/0.99  --bmc1_ucm_cone_mode                    none
% 0.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.98/0.99  --bmc1_ucm_relax_model                  4
% 0.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/0.99  --bmc1_ucm_layered_model                none
% 0.98/0.99  --bmc1_ucm_max_lemma_size               10
% 0.98/0.99  
% 0.98/0.99  ------ AIG Options
% 0.98/0.99  
% 0.98/0.99  --aig_mode                              false
% 0.98/0.99  
% 0.98/0.99  ------ Instantiation Options
% 0.98/0.99  
% 0.98/0.99  --instantiation_flag                    true
% 0.98/0.99  --inst_sos_flag                         false
% 0.98/0.99  --inst_sos_phase                        true
% 0.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/0.99  --inst_lit_sel_side                     num_symb
% 0.98/0.99  --inst_solver_per_active                1400
% 0.98/0.99  --inst_solver_calls_frac                1.
% 0.98/0.99  --inst_passive_queue_type               priority_queues
% 0.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/0.99  --inst_passive_queues_freq              [25;2]
% 0.98/0.99  --inst_dismatching                      true
% 0.98/0.99  --inst_eager_unprocessed_to_passive     true
% 0.98/0.99  --inst_prop_sim_given                   true
% 0.98/0.99  --inst_prop_sim_new                     false
% 0.98/0.99  --inst_subs_new                         false
% 0.98/0.99  --inst_eq_res_simp                      false
% 0.98/0.99  --inst_subs_given                       false
% 0.98/0.99  --inst_orphan_elimination               true
% 0.98/0.99  --inst_learning_loop_flag               true
% 0.98/0.99  --inst_learning_start                   3000
% 0.98/0.99  --inst_learning_factor                  2
% 0.98/0.99  --inst_start_prop_sim_after_learn       3
% 0.98/0.99  --inst_sel_renew                        solver
% 0.98/0.99  --inst_lit_activity_flag                true
% 0.98/0.99  --inst_restr_to_given                   false
% 0.98/0.99  --inst_activity_threshold               500
% 0.98/0.99  --inst_out_proof                        true
% 0.98/0.99  
% 0.98/0.99  ------ Resolution Options
% 0.98/0.99  
% 0.98/0.99  --resolution_flag                       true
% 0.98/0.99  --res_lit_sel                           adaptive
% 0.98/0.99  --res_lit_sel_side                      none
% 0.98/0.99  --res_ordering                          kbo
% 0.98/0.99  --res_to_prop_solver                    active
% 0.98/0.99  --res_prop_simpl_new                    false
% 0.98/0.99  --res_prop_simpl_given                  true
% 0.98/0.99  --res_passive_queue_type                priority_queues
% 0.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/0.99  --res_passive_queues_freq               [15;5]
% 0.98/0.99  --res_forward_subs                      full
% 0.98/0.99  --res_backward_subs                     full
% 0.98/0.99  --res_forward_subs_resolution           true
% 0.98/0.99  --res_backward_subs_resolution          true
% 0.98/0.99  --res_orphan_elimination                true
% 0.98/0.99  --res_time_limit                        2.
% 0.98/0.99  --res_out_proof                         true
% 0.98/0.99  
% 0.98/0.99  ------ Superposition Options
% 0.98/0.99  
% 0.98/0.99  --superposition_flag                    true
% 0.98/0.99  --sup_passive_queue_type                priority_queues
% 0.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.98/0.99  --demod_completeness_check              fast
% 0.98/0.99  --demod_use_ground                      true
% 0.98/0.99  --sup_to_prop_solver                    passive
% 0.98/0.99  --sup_prop_simpl_new                    true
% 0.98/0.99  --sup_prop_simpl_given                  true
% 0.98/0.99  --sup_fun_splitting                     false
% 0.98/0.99  --sup_smt_interval                      50000
% 0.98/0.99  
% 0.98/0.99  ------ Superposition Simplification Setup
% 0.98/0.99  
% 0.98/0.99  --sup_indices_passive                   []
% 0.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_full_bw                           [BwDemod]
% 0.98/0.99  --sup_immed_triv                        [TrivRules]
% 0.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_immed_bw_main                     []
% 0.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.99  
% 0.98/0.99  ------ Combination Options
% 0.98/0.99  
% 0.98/0.99  --comb_res_mult                         3
% 0.98/0.99  --comb_sup_mult                         2
% 0.98/0.99  --comb_inst_mult                        10
% 0.98/0.99  
% 0.98/0.99  ------ Debug Options
% 0.98/0.99  
% 0.98/0.99  --dbg_backtrace                         false
% 0.98/0.99  --dbg_dump_prop_clauses                 false
% 0.98/0.99  --dbg_dump_prop_clauses_file            -
% 0.98/0.99  --dbg_out_stat                          false
% 0.98/0.99  ------ Parsing...
% 0.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.98/0.99  
% 0.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.98/0.99  
% 0.98/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.98/0.99  
% 0.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.98/0.99  ------ Proving...
% 0.98/0.99  ------ Problem Properties 
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  clauses                                 14
% 0.98/0.99  conjectures                             8
% 0.98/0.99  EPR                                     4
% 0.98/0.99  Horn                                    14
% 0.98/0.99  unary                                   11
% 0.98/0.99  binary                                  2
% 0.98/0.99  lits                                    22
% 0.98/0.99  lits eq                                 5
% 0.98/0.99  fd_pure                                 0
% 0.98/0.99  fd_pseudo                               0
% 0.98/0.99  fd_cond                                 0
% 0.98/0.99  fd_pseudo_cond                          0
% 0.98/0.99  AC symbols                              0
% 0.98/0.99  
% 0.98/0.99  ------ Schedule dynamic 5 is on 
% 0.98/0.99  
% 0.98/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  ------ 
% 0.98/0.99  Current options:
% 0.98/0.99  ------ 
% 0.98/0.99  
% 0.98/0.99  ------ Input Options
% 0.98/0.99  
% 0.98/0.99  --out_options                           all
% 0.98/0.99  --tptp_safe_out                         true
% 0.98/0.99  --problem_path                          ""
% 0.98/0.99  --include_path                          ""
% 0.98/0.99  --clausifier                            res/vclausify_rel
% 0.98/0.99  --clausifier_options                    --mode clausify
% 0.98/0.99  --stdin                                 false
% 0.98/0.99  --stats_out                             all
% 0.98/0.99  
% 0.98/0.99  ------ General Options
% 0.98/0.99  
% 0.98/0.99  --fof                                   false
% 0.98/0.99  --time_out_real                         305.
% 0.98/0.99  --time_out_virtual                      -1.
% 0.98/0.99  --symbol_type_check                     false
% 0.98/0.99  --clausify_out                          false
% 0.98/0.99  --sig_cnt_out                           false
% 0.98/0.99  --trig_cnt_out                          false
% 0.98/0.99  --trig_cnt_out_tolerance                1.
% 0.98/0.99  --trig_cnt_out_sk_spl                   false
% 0.98/0.99  --abstr_cl_out                          false
% 0.98/0.99  
% 0.98/0.99  ------ Global Options
% 0.98/0.99  
% 0.98/0.99  --schedule                              default
% 0.98/0.99  --add_important_lit                     false
% 0.98/0.99  --prop_solver_per_cl                    1000
% 0.98/0.99  --min_unsat_core                        false
% 0.98/0.99  --soft_assumptions                      false
% 0.98/0.99  --soft_lemma_size                       3
% 0.98/0.99  --prop_impl_unit_size                   0
% 0.98/0.99  --prop_impl_unit                        []
% 0.98/0.99  --share_sel_clauses                     true
% 0.98/0.99  --reset_solvers                         false
% 0.98/0.99  --bc_imp_inh                            [conj_cone]
% 0.98/0.99  --conj_cone_tolerance                   3.
% 0.98/0.99  --extra_neg_conj                        none
% 0.98/0.99  --large_theory_mode                     true
% 0.98/0.99  --prolific_symb_bound                   200
% 0.98/0.99  --lt_threshold                          2000
% 0.98/0.99  --clause_weak_htbl                      true
% 0.98/0.99  --gc_record_bc_elim                     false
% 0.98/0.99  
% 0.98/0.99  ------ Preprocessing Options
% 0.98/0.99  
% 0.98/0.99  --preprocessing_flag                    true
% 0.98/0.99  --time_out_prep_mult                    0.1
% 0.98/0.99  --splitting_mode                        input
% 0.98/0.99  --splitting_grd                         true
% 0.98/0.99  --splitting_cvd                         false
% 0.98/0.99  --splitting_cvd_svl                     false
% 0.98/0.99  --splitting_nvd                         32
% 0.98/0.99  --sub_typing                            true
% 0.98/0.99  --prep_gs_sim                           true
% 0.98/0.99  --prep_unflatten                        true
% 0.98/0.99  --prep_res_sim                          true
% 0.98/0.99  --prep_upred                            true
% 0.98/0.99  --prep_sem_filter                       exhaustive
% 0.98/0.99  --prep_sem_filter_out                   false
% 0.98/0.99  --pred_elim                             true
% 0.98/0.99  --res_sim_input                         true
% 0.98/0.99  --eq_ax_congr_red                       true
% 0.98/0.99  --pure_diseq_elim                       true
% 0.98/0.99  --brand_transform                       false
% 0.98/0.99  --non_eq_to_eq                          false
% 0.98/0.99  --prep_def_merge                        true
% 0.98/0.99  --prep_def_merge_prop_impl              false
% 0.98/0.99  --prep_def_merge_mbd                    true
% 0.98/0.99  --prep_def_merge_tr_red                 false
% 0.98/0.99  --prep_def_merge_tr_cl                  false
% 0.98/0.99  --smt_preprocessing                     true
% 0.98/0.99  --smt_ac_axioms                         fast
% 0.98/0.99  --preprocessed_out                      false
% 0.98/0.99  --preprocessed_stats                    false
% 0.98/0.99  
% 0.98/0.99  ------ Abstraction refinement Options
% 0.98/0.99  
% 0.98/0.99  --abstr_ref                             []
% 0.98/0.99  --abstr_ref_prep                        false
% 0.98/0.99  --abstr_ref_until_sat                   false
% 0.98/0.99  --abstr_ref_sig_restrict                funpre
% 0.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/0.99  --abstr_ref_under                       []
% 0.98/0.99  
% 0.98/0.99  ------ SAT Options
% 0.98/0.99  
% 0.98/0.99  --sat_mode                              false
% 0.98/0.99  --sat_fm_restart_options                ""
% 0.98/0.99  --sat_gr_def                            false
% 0.98/0.99  --sat_epr_types                         true
% 0.98/0.99  --sat_non_cyclic_types                  false
% 0.98/0.99  --sat_finite_models                     false
% 0.98/0.99  --sat_fm_lemmas                         false
% 0.98/0.99  --sat_fm_prep                           false
% 0.98/0.99  --sat_fm_uc_incr                        true
% 0.98/0.99  --sat_out_model                         small
% 0.98/0.99  --sat_out_clauses                       false
% 0.98/0.99  
% 0.98/0.99  ------ QBF Options
% 0.98/0.99  
% 0.98/0.99  --qbf_mode                              false
% 0.98/0.99  --qbf_elim_univ                         false
% 0.98/0.99  --qbf_dom_inst                          none
% 0.98/0.99  --qbf_dom_pre_inst                      false
% 0.98/0.99  --qbf_sk_in                             false
% 0.98/0.99  --qbf_pred_elim                         true
% 0.98/0.99  --qbf_split                             512
% 0.98/0.99  
% 0.98/0.99  ------ BMC1 Options
% 0.98/0.99  
% 0.98/0.99  --bmc1_incremental                      false
% 0.98/0.99  --bmc1_axioms                           reachable_all
% 0.98/0.99  --bmc1_min_bound                        0
% 0.98/0.99  --bmc1_max_bound                        -1
% 0.98/0.99  --bmc1_max_bound_default                -1
% 0.98/0.99  --bmc1_symbol_reachability              true
% 0.98/0.99  --bmc1_property_lemmas                  false
% 0.98/0.99  --bmc1_k_induction                      false
% 0.98/0.99  --bmc1_non_equiv_states                 false
% 0.98/0.99  --bmc1_deadlock                         false
% 0.98/0.99  --bmc1_ucm                              false
% 0.98/0.99  --bmc1_add_unsat_core                   none
% 0.98/0.99  --bmc1_unsat_core_children              false
% 0.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/0.99  --bmc1_out_stat                         full
% 0.98/0.99  --bmc1_ground_init                      false
% 0.98/0.99  --bmc1_pre_inst_next_state              false
% 0.98/0.99  --bmc1_pre_inst_state                   false
% 0.98/0.99  --bmc1_pre_inst_reach_state             false
% 0.98/0.99  --bmc1_out_unsat_core                   false
% 0.98/0.99  --bmc1_aig_witness_out                  false
% 0.98/0.99  --bmc1_verbose                          false
% 0.98/0.99  --bmc1_dump_clauses_tptp                false
% 0.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.98/0.99  --bmc1_dump_file                        -
% 0.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.98/0.99  --bmc1_ucm_extend_mode                  1
% 0.98/0.99  --bmc1_ucm_init_mode                    2
% 0.98/0.99  --bmc1_ucm_cone_mode                    none
% 0.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.98/0.99  --bmc1_ucm_relax_model                  4
% 0.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/0.99  --bmc1_ucm_layered_model                none
% 0.98/0.99  --bmc1_ucm_max_lemma_size               10
% 0.98/0.99  
% 0.98/0.99  ------ AIG Options
% 0.98/0.99  
% 0.98/0.99  --aig_mode                              false
% 0.98/0.99  
% 0.98/0.99  ------ Instantiation Options
% 0.98/0.99  
% 0.98/0.99  --instantiation_flag                    true
% 0.98/0.99  --inst_sos_flag                         false
% 0.98/0.99  --inst_sos_phase                        true
% 0.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/0.99  --inst_lit_sel_side                     none
% 0.98/0.99  --inst_solver_per_active                1400
% 0.98/0.99  --inst_solver_calls_frac                1.
% 0.98/0.99  --inst_passive_queue_type               priority_queues
% 0.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/0.99  --inst_passive_queues_freq              [25;2]
% 0.98/0.99  --inst_dismatching                      true
% 0.98/0.99  --inst_eager_unprocessed_to_passive     true
% 0.98/0.99  --inst_prop_sim_given                   true
% 0.98/0.99  --inst_prop_sim_new                     false
% 0.98/0.99  --inst_subs_new                         false
% 0.98/0.99  --inst_eq_res_simp                      false
% 0.98/0.99  --inst_subs_given                       false
% 0.98/0.99  --inst_orphan_elimination               true
% 0.98/0.99  --inst_learning_loop_flag               true
% 0.98/0.99  --inst_learning_start                   3000
% 0.98/0.99  --inst_learning_factor                  2
% 0.98/0.99  --inst_start_prop_sim_after_learn       3
% 0.98/0.99  --inst_sel_renew                        solver
% 0.98/0.99  --inst_lit_activity_flag                true
% 0.98/0.99  --inst_restr_to_given                   false
% 0.98/0.99  --inst_activity_threshold               500
% 0.98/0.99  --inst_out_proof                        true
% 0.98/0.99  
% 0.98/0.99  ------ Resolution Options
% 0.98/0.99  
% 0.98/0.99  --resolution_flag                       false
% 0.98/0.99  --res_lit_sel                           adaptive
% 0.98/0.99  --res_lit_sel_side                      none
% 0.98/0.99  --res_ordering                          kbo
% 0.98/0.99  --res_to_prop_solver                    active
% 0.98/0.99  --res_prop_simpl_new                    false
% 0.98/0.99  --res_prop_simpl_given                  true
% 0.98/0.99  --res_passive_queue_type                priority_queues
% 0.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/0.99  --res_passive_queues_freq               [15;5]
% 0.98/0.99  --res_forward_subs                      full
% 0.98/0.99  --res_backward_subs                     full
% 0.98/0.99  --res_forward_subs_resolution           true
% 0.98/0.99  --res_backward_subs_resolution          true
% 0.98/0.99  --res_orphan_elimination                true
% 0.98/0.99  --res_time_limit                        2.
% 0.98/0.99  --res_out_proof                         true
% 0.98/0.99  
% 0.98/0.99  ------ Superposition Options
% 0.98/0.99  
% 0.98/0.99  --superposition_flag                    true
% 0.98/0.99  --sup_passive_queue_type                priority_queues
% 0.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.98/0.99  --demod_completeness_check              fast
% 0.98/0.99  --demod_use_ground                      true
% 0.98/0.99  --sup_to_prop_solver                    passive
% 0.98/0.99  --sup_prop_simpl_new                    true
% 0.98/0.99  --sup_prop_simpl_given                  true
% 0.98/0.99  --sup_fun_splitting                     false
% 0.98/0.99  --sup_smt_interval                      50000
% 0.98/0.99  
% 0.98/0.99  ------ Superposition Simplification Setup
% 0.98/0.99  
% 0.98/0.99  --sup_indices_passive                   []
% 0.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_full_bw                           [BwDemod]
% 0.98/0.99  --sup_immed_triv                        [TrivRules]
% 0.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_immed_bw_main                     []
% 0.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.99  
% 0.98/0.99  ------ Combination Options
% 0.98/0.99  
% 0.98/0.99  --comb_res_mult                         3
% 0.98/0.99  --comb_sup_mult                         2
% 0.98/0.99  --comb_inst_mult                        10
% 0.98/0.99  
% 0.98/0.99  ------ Debug Options
% 0.98/0.99  
% 0.98/0.99  --dbg_backtrace                         false
% 0.98/0.99  --dbg_dump_prop_clauses                 false
% 0.98/0.99  --dbg_dump_prop_clauses_file            -
% 0.98/0.99  --dbg_out_stat                          false
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  ------ Proving...
% 0.98/0.99  
% 0.98/0.99  
% 0.98/0.99  % SZS status Theorem for theBenchmark.p
% 0.98/0.99  
% 0.98/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.98/0.99  
% 0.98/0.99  fof(f9,conjecture,(
% 0.98/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5) => r1_orders_2(X2,X5,X6)))))))))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f10,negated_conjecture,(
% 0.98/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5) => r1_orders_2(X2,X5,X6)))))))))),
% 0.98/0.99    inference(negated_conjecture,[],[f9])).
% 0.98/0.99  
% 0.98/0.99  fof(f23,plain,(
% 0.98/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X2,X5,X6) & (r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & (m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.98/0.99    inference(ennf_transformation,[],[f10])).
% 0.98/0.99  
% 0.98/0.99  fof(f24,plain,(
% 0.98/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.98/0.99    inference(flattening,[],[f23])).
% 0.98/0.99  
% 0.98/0.99  fof(f33,plain,(
% 0.98/0.99    ( ! [X4,X2,X5,X3,X1] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_orders_2(X2,X5,sK6) & r1_orders_2(X1,X3,X4) & sK6 = X4 & X3 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 0.98/0.99    introduced(choice_axiom,[])).
% 0.98/0.99  
% 0.98/0.99  fof(f32,plain,(
% 0.98/0.99    ( ! [X4,X2,X3,X1] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) => (? [X6] : (~r1_orders_2(X2,sK5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & sK5 = X3 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X2)))) )),
% 0.98/0.99    introduced(choice_axiom,[])).
% 0.98/0.99  
% 0.98/0.99  fof(f31,plain,(
% 0.98/0.99    ( ! [X2,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,sK4) & sK4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 0.98/0.99    introduced(choice_axiom,[])).
% 0.98/0.99  
% 0.98/0.99  fof(f30,plain,(
% 0.98/0.99    ( ! [X2,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,sK3,X4) & X4 = X6 & sK3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3,u1_struct_0(X1)))) )),
% 0.98/0.99    introduced(choice_axiom,[])).
% 0.98/0.99  
% 0.98/0.99  fof(f29,plain,(
% 0.98/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(sK2,X0,X1) & v2_yellow_6(sK2,X0,X1) & ~v2_struct_0(sK2))) )),
% 0.98/0.99    introduced(choice_axiom,[])).
% 0.98/0.99  
% 0.98/0.99  fof(f28,plain,(
% 0.98/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(sK1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_yellow_6(X2,X0,sK1) & v2_yellow_6(X2,X0,sK1) & ~v2_struct_0(X2)) & l1_waybel_0(sK1,X0) & ~v2_struct_0(sK1))) )),
% 0.98/0.99    introduced(choice_axiom,[])).
% 0.98/0.99  
% 0.98/0.99  fof(f27,plain,(
% 0.98/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,sK0,X1) & v2_yellow_6(X2,sK0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.98/0.99    introduced(choice_axiom,[])).
% 0.98/0.99  
% 0.98/0.99  fof(f34,plain,(
% 0.98/0.99    ((((((~r1_orders_2(sK2,sK5,sK6) & r1_orders_2(sK1,sK3,sK4) & sK4 = sK6 & sK3 = sK5 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_yellow_6(sK2,sK0,sK1) & v2_yellow_6(sK2,sK0,sK1) & ~v2_struct_0(sK2)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f24,f33,f32,f31,f30,f29,f28,f27])).
% 0.98/0.99  
% 0.98/0.99  fof(f52,plain,(
% 0.98/0.99    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f2,axiom,(
% 0.98/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f13,plain,(
% 0.98/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.98/0.99    inference(ennf_transformation,[],[f2])).
% 0.98/0.99  
% 0.98/0.99  fof(f36,plain,(
% 0.98/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f13])).
% 0.98/0.99  
% 0.98/0.99  fof(f4,axiom,(
% 0.98/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f16,plain,(
% 0.98/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(ennf_transformation,[],[f4])).
% 0.98/0.99  
% 0.98/0.99  fof(f38,plain,(
% 0.98/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f16])).
% 0.98/0.99  
% 0.98/0.99  fof(f6,axiom,(
% 0.98/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f19,plain,(
% 0.98/0.99    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.98/0.99    inference(ennf_transformation,[],[f6])).
% 0.98/0.99  
% 0.98/0.99  fof(f40,plain,(
% 0.98/0.99    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f19])).
% 0.98/0.99  
% 0.98/0.99  fof(f47,plain,(
% 0.98/0.99    l1_waybel_0(sK1,sK0)),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f45,plain,(
% 0.98/0.99    l1_struct_0(sK0)),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f56,plain,(
% 0.98/0.99    sK4 = sK6),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f51,plain,(
% 0.98/0.99    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f55,plain,(
% 0.98/0.99    sK3 = sK5),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f5,axiom,(
% 0.98/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r2_hidden(X4,u1_struct_0(X1)) & r1_orders_2(X0,X2,X3) & X3 = X5 & X2 = X4) => r1_orders_2(X1,X4,X5))))))))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f17,plain,(
% 0.98/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_orders_2(X1,X4,X5) | (~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0))) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(ennf_transformation,[],[f5])).
% 0.98/0.99  
% 0.98/0.99  fof(f18,plain,(
% 0.98/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.98/0.99    inference(flattening,[],[f17])).
% 0.98/0.99  
% 0.98/0.99  fof(f39,plain,(
% 0.98/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f18])).
% 0.98/0.99  
% 0.98/0.99  fof(f59,plain,(
% 0.98/0.99    ( ! [X4,X2,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X5) | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.98/0.99    inference(equality_resolution,[],[f39])).
% 0.98/0.99  
% 0.98/0.99  fof(f60,plain,(
% 0.98/0.99    ( ! [X4,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 0.98/0.99    inference(equality_resolution,[],[f59])).
% 0.98/0.99  
% 0.98/0.99  fof(f7,axiom,(
% 0.98/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => (v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))))))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f20,plain,(
% 0.98/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.98/0.99    inference(ennf_transformation,[],[f7])).
% 0.98/0.99  
% 0.98/0.99  fof(f25,plain,(
% 0.98/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_yellow_6(X2,X0,X1) | (~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1))) & ((m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1)) | ~v2_yellow_6(X2,X0,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.98/0.99    inference(nnf_transformation,[],[f20])).
% 0.98/0.99  
% 0.98/0.99  fof(f26,plain,(
% 0.98/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_yellow_6(X2,X0,X1) | ~m1_yellow_0(X2,X1) | ~v4_yellow_0(X2,X1)) & ((m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1)) | ~v2_yellow_6(X2,X0,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.98/0.99    inference(flattening,[],[f25])).
% 0.98/0.99  
% 0.98/0.99  fof(f42,plain,(
% 0.98/0.99    ( ! [X2,X0,X1] : (m1_yellow_0(X2,X1) | ~v2_yellow_6(X2,X0,X1) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f26])).
% 0.98/0.99  
% 0.98/0.99  fof(f50,plain,(
% 0.98/0.99    m1_yellow_6(sK2,sK0,sK1)),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f49,plain,(
% 0.98/0.99    v2_yellow_6(sK2,sK0,sK1)),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f41,plain,(
% 0.98/0.99    ( ! [X2,X0,X1] : (v4_yellow_0(X2,X1) | ~v2_yellow_6(X2,X0,X1) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f26])).
% 0.98/0.99  
% 0.98/0.99  fof(f8,axiom,(
% 0.98/0.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f21,plain,(
% 0.98/0.99    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.98/0.99    inference(ennf_transformation,[],[f8])).
% 0.98/0.99  
% 0.98/0.99  fof(f22,plain,(
% 0.98/0.99    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.98/0.99    inference(flattening,[],[f21])).
% 0.98/0.99  
% 0.98/0.99  fof(f44,plain,(
% 0.98/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f22])).
% 0.98/0.99  
% 0.98/0.99  fof(f1,axiom,(
% 0.98/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f11,plain,(
% 0.98/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.98/0.99    inference(ennf_transformation,[],[f1])).
% 0.98/0.99  
% 0.98/0.99  fof(f12,plain,(
% 0.98/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.98/0.99    inference(flattening,[],[f11])).
% 0.98/0.99  
% 0.98/0.99  fof(f35,plain,(
% 0.98/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f12])).
% 0.98/0.99  
% 0.98/0.99  fof(f3,axiom,(
% 0.98/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/0.99  
% 0.98/0.99  fof(f14,plain,(
% 0.98/0.99    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.98/0.99    inference(ennf_transformation,[],[f3])).
% 0.98/0.99  
% 0.98/0.99  fof(f15,plain,(
% 0.98/0.99    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.98/0.99    inference(flattening,[],[f14])).
% 0.98/0.99  
% 0.98/0.99  fof(f37,plain,(
% 0.98/0.99    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.98/0.99    inference(cnf_transformation,[],[f15])).
% 0.98/0.99  
% 0.98/0.99  fof(f48,plain,(
% 0.98/0.99    ~v2_struct_0(sK2)),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f53,plain,(
% 0.98/0.99    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f54,plain,(
% 0.98/0.99    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f57,plain,(
% 0.98/0.99    r1_orders_2(sK1,sK3,sK4)),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  fof(f58,plain,(
% 0.98/0.99    ~r1_orders_2(sK2,sK5,sK6)),
% 0.98/0.99    inference(cnf_transformation,[],[f34])).
% 0.98/0.99  
% 0.98/0.99  cnf(c_16,negated_conjecture,
% 0.98/0.99      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 0.98/0.99      inference(cnf_transformation,[],[f52]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_741,negated_conjecture,
% 0.98/0.99      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 0.98/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_941,plain,
% 0.98/0.99      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 0.98/0.99      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_1,plain,
% 0.98/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.98/0.99      inference(cnf_transformation,[],[f36]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_3,plain,
% 0.98/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 0.98/0.99      inference(cnf_transformation,[],[f38]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_5,plain,
% 0.98/0.99      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | ~ l1_struct_0(X1) ),
% 0.98/0.99      inference(cnf_transformation,[],[f40]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_21,negated_conjecture,
% 0.98/0.99      ( l1_waybel_0(sK1,sK0) ),
% 0.98/0.99      inference(cnf_transformation,[],[f47]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_409,plain,
% 0.98/0.99      ( l1_orders_2(X0) | ~ l1_struct_0(X1) | sK0 != X1 | sK1 != X0 ),
% 0.98/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_410,plain,
% 0.98/0.99      ( l1_orders_2(sK1) | ~ l1_struct_0(sK0) ),
% 0.98/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_23,negated_conjecture,
% 0.98/0.99      ( l1_struct_0(sK0) ),
% 0.98/0.99      inference(cnf_transformation,[],[f45]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_412,plain,
% 0.98/0.99      ( l1_orders_2(sK1) ),
% 0.98/0.99      inference(global_propositional_subsumption,
% 0.98/0.99                [status(thm)],
% 0.98/0.99                [c_410,c_23]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_476,plain,
% 0.98/0.99      ( l1_struct_0(X0) | sK1 != X0 ),
% 0.98/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_412]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_477,plain,
% 0.98/0.99      ( l1_struct_0(sK1) ),
% 0.98/0.99      inference(unflattening,[status(thm)],[c_476]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_507,plain,
% 0.98/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 0.98/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_477]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_508,plain,
% 0.98/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.98/0.99      inference(unflattening,[status(thm)],[c_507]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_735,plain,
% 0.98/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.98/0.99      inference(subtyping,[status(esa)],[c_508]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_12,negated_conjecture,
% 0.98/0.99      ( sK4 = sK6 ),
% 0.98/0.99      inference(cnf_transformation,[],[f56]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_745,negated_conjecture,
% 0.98/0.99      ( sK4 = sK6 ),
% 0.98/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_965,plain,
% 0.98/0.99      ( m1_subset_1(sK6,k2_struct_0(sK1)) = iProver_top ),
% 0.98/0.99      inference(light_normalisation,[status(thm)],[c_941,c_735,c_745]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_17,negated_conjecture,
% 0.98/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 0.98/0.99      inference(cnf_transformation,[],[f51]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_740,negated_conjecture,
% 0.98/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 0.98/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 0.98/0.99  
% 0.98/0.99  cnf(c_942,plain,
% 0.98/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 0.98/0.99      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_13,negated_conjecture,
% 0.98/1.00      ( sK3 = sK5 ),
% 0.98/1.00      inference(cnf_transformation,[],[f55]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_744,negated_conjecture,
% 0.98/1.00      ( sK3 = sK5 ),
% 0.98/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_968,plain,
% 0.98/1.00      ( m1_subset_1(sK5,k2_struct_0(sK1)) = iProver_top ),
% 0.98/1.00      inference(light_normalisation,[status(thm)],[c_942,c_735,c_744]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_4,plain,
% 0.98/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 0.98/1.00      | r1_orders_2(X3,X1,X2)
% 0.98/1.00      | ~ v4_yellow_0(X3,X0)
% 0.98/1.00      | ~ m1_yellow_0(X3,X0)
% 0.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X3))
% 0.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.98/1.00      | ~ r2_hidden(X1,u1_struct_0(X3))
% 0.98/1.00      | ~ l1_orders_2(X0) ),
% 0.98/1.00      inference(cnf_transformation,[],[f60]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_7,plain,
% 0.98/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 0.98/1.00      | ~ v2_yellow_6(X0,X1,X2)
% 0.98/1.00      | ~ l1_waybel_0(X2,X1)
% 0.98/1.00      | m1_yellow_0(X0,X2)
% 0.98/1.00      | ~ l1_struct_0(X1) ),
% 0.98/1.00      inference(cnf_transformation,[],[f42]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_18,negated_conjecture,
% 0.98/1.00      ( m1_yellow_6(sK2,sK0,sK1) ),
% 0.98/1.00      inference(cnf_transformation,[],[f50]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_390,plain,
% 0.98/1.00      ( ~ v2_yellow_6(X0,X1,X2)
% 0.98/1.00      | ~ l1_waybel_0(X2,X1)
% 0.98/1.00      | m1_yellow_0(X0,X2)
% 0.98/1.00      | ~ l1_struct_0(X1)
% 0.98/1.00      | sK0 != X1
% 0.98/1.00      | sK1 != X2
% 0.98/1.00      | sK2 != X0 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_391,plain,
% 0.98/1.00      ( ~ v2_yellow_6(sK2,sK0,sK1)
% 0.98/1.00      | ~ l1_waybel_0(sK1,sK0)
% 0.98/1.00      | m1_yellow_0(sK2,sK1)
% 0.98/1.00      | ~ l1_struct_0(sK0) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_390]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_19,negated_conjecture,
% 0.98/1.00      ( v2_yellow_6(sK2,sK0,sK1) ),
% 0.98/1.00      inference(cnf_transformation,[],[f49]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_393,plain,
% 0.98/1.00      ( m1_yellow_0(sK2,sK1) ),
% 0.98/1.00      inference(global_propositional_subsumption,
% 0.98/1.00                [status(thm)],
% 0.98/1.00                [c_391,c_23,c_21,c_19]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_435,plain,
% 0.98/1.00      ( ~ r1_orders_2(X0,X1,X2)
% 0.98/1.00      | r1_orders_2(X3,X1,X2)
% 0.98/1.00      | ~ v4_yellow_0(X3,X0)
% 0.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 0.98/1.00      | ~ m1_subset_1(X2,u1_struct_0(X3))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X3))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 0.98/1.00      | ~ r2_hidden(X1,u1_struct_0(X3))
% 0.98/1.00      | ~ l1_orders_2(X0)
% 0.98/1.00      | sK1 != X0
% 0.98/1.00      | sK2 != X3 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_393]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_436,plain,
% 0.98/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 0.98/1.00      | r1_orders_2(sK2,X0,X1)
% 0.98/1.00      | ~ v4_yellow_0(sK2,sK1)
% 0.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.98/1.00      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 0.98/1.00      | ~ l1_orders_2(sK1) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_8,plain,
% 0.98/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 0.98/1.00      | ~ v2_yellow_6(X0,X1,X2)
% 0.98/1.00      | ~ l1_waybel_0(X2,X1)
% 0.98/1.00      | v4_yellow_0(X0,X2)
% 0.98/1.00      | ~ l1_struct_0(X1) ),
% 0.98/1.00      inference(cnf_transformation,[],[f41]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_379,plain,
% 0.98/1.00      ( ~ v2_yellow_6(X0,X1,X2)
% 0.98/1.00      | ~ l1_waybel_0(X2,X1)
% 0.98/1.00      | v4_yellow_0(X0,X2)
% 0.98/1.00      | ~ l1_struct_0(X1)
% 0.98/1.00      | sK0 != X1
% 0.98/1.00      | sK1 != X2
% 0.98/1.00      | sK2 != X0 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_380,plain,
% 0.98/1.00      ( ~ v2_yellow_6(sK2,sK0,sK1)
% 0.98/1.00      | ~ l1_waybel_0(sK1,sK0)
% 0.98/1.00      | v4_yellow_0(sK2,sK1)
% 0.98/1.00      | ~ l1_struct_0(sK0) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_379]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_440,plain,
% 0.98/1.00      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.98/1.00      | ~ r1_orders_2(sK1,X0,X1)
% 0.98/1.00      | r1_orders_2(sK2,X0,X1) ),
% 0.98/1.00      inference(global_propositional_subsumption,
% 0.98/1.00                [status(thm)],
% 0.98/1.00                [c_436,c_23,c_21,c_19,c_380,c_410]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_441,plain,
% 0.98/1.00      ( ~ r1_orders_2(sK1,X0,X1)
% 0.98/1.00      | r1_orders_2(sK2,X0,X1)
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 0.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 0.98/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 0.98/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.98/1.00      | ~ r2_hidden(X0,u1_struct_0(sK2)) ),
% 0.98/1.00      inference(renaming,[status(thm)],[c_440]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_739,plain,
% 0.98/1.00      ( ~ r1_orders_2(sK1,X0_51,X1_51)
% 0.98/1.00      | r1_orders_2(sK2,X0_51,X1_51)
% 0.98/1.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK1))
% 0.98/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 0.98/1.00      | ~ m1_subset_1(X1_51,u1_struct_0(sK2))
% 0.98/1.00      | ~ m1_subset_1(X0_51,u1_struct_0(sK2))
% 0.98/1.00      | ~ r2_hidden(X0_51,u1_struct_0(sK2)) ),
% 0.98/1.00      inference(subtyping,[status(esa)],[c_441]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_943,plain,
% 0.98/1.00      ( r1_orders_2(sK1,X0_51,X1_51) != iProver_top
% 0.98/1.00      | r1_orders_2(sK2,X0_51,X1_51) = iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top
% 0.98/1.00      | m1_subset_1(X1_51,u1_struct_0(sK1)) != iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 0.98/1.00      | m1_subset_1(X1_51,u1_struct_0(sK2)) != iProver_top
% 0.98/1.00      | r2_hidden(X0_51,u1_struct_0(sK2)) != iProver_top ),
% 0.98/1.00      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_9,plain,
% 0.98/1.00      ( ~ m1_yellow_6(X0,X1,X2)
% 0.98/1.00      | ~ l1_waybel_0(X2,X1)
% 0.98/1.00      | l1_waybel_0(X0,X1)
% 0.98/1.00      | ~ l1_struct_0(X1) ),
% 0.98/1.00      inference(cnf_transformation,[],[f44]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_368,plain,
% 0.98/1.00      ( ~ l1_waybel_0(X0,X1)
% 0.98/1.00      | l1_waybel_0(X2,X1)
% 0.98/1.00      | ~ l1_struct_0(X1)
% 0.98/1.00      | sK0 != X1
% 0.98/1.00      | sK1 != X0
% 0.98/1.00      | sK2 != X2 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_369,plain,
% 0.98/1.00      ( ~ l1_waybel_0(sK1,sK0)
% 0.98/1.00      | l1_waybel_0(sK2,sK0)
% 0.98/1.00      | ~ l1_struct_0(sK0) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_368]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_371,plain,
% 0.98/1.00      ( l1_waybel_0(sK2,sK0) ),
% 0.98/1.00      inference(global_propositional_subsumption,
% 0.98/1.00                [status(thm)],
% 0.98/1.00                [c_369,c_23,c_21]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_420,plain,
% 0.98/1.00      ( l1_orders_2(X0) | ~ l1_struct_0(X1) | sK0 != X1 | sK2 != X0 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_371]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_421,plain,
% 0.98/1.00      ( l1_orders_2(sK2) | ~ l1_struct_0(sK0) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_423,plain,
% 0.98/1.00      ( l1_orders_2(sK2) ),
% 0.98/1.00      inference(global_propositional_subsumption,
% 0.98/1.00                [status(thm)],
% 0.98/1.00                [c_421,c_23]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_483,plain,
% 0.98/1.00      ( l1_struct_0(X0) | sK2 != X0 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_423]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_484,plain,
% 0.98/1.00      ( l1_struct_0(sK2) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_483]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_512,plain,
% 0.98/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_484]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_513,plain,
% 0.98/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_734,plain,
% 0.98/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 0.98/1.00      inference(subtyping,[status(esa)],[c_513]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_981,plain,
% 0.98/1.00      ( r1_orders_2(sK1,X0_51,X1_51) != iProver_top
% 0.98/1.00      | r1_orders_2(sK2,X0_51,X1_51) = iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
% 0.98/1.00      | m1_subset_1(X1_51,k2_struct_0(sK1)) != iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
% 0.98/1.00      | m1_subset_1(X1_51,k2_struct_0(sK2)) != iProver_top
% 0.98/1.00      | r2_hidden(X0_51,k2_struct_0(sK2)) != iProver_top ),
% 0.98/1.00      inference(light_normalisation,[status(thm)],[c_943,c_734,c_735]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_0,plain,
% 0.98/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 0.98/1.00      inference(cnf_transformation,[],[f35]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_2,plain,
% 0.98/1.00      ( v2_struct_0(X0)
% 0.98/1.00      | ~ l1_struct_0(X0)
% 0.98/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 0.98/1.00      inference(cnf_transformation,[],[f37]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_20,negated_conjecture,
% 0.98/1.00      ( ~ v2_struct_0(sK2) ),
% 0.98/1.00      inference(cnf_transformation,[],[f48]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_253,plain,
% 0.98/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK2 != X0 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_254,plain,
% 0.98/1.00      ( ~ l1_struct_0(sK2) | ~ v1_xboole_0(k2_struct_0(sK2)) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_253]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_294,plain,
% 0.98/1.00      ( ~ m1_subset_1(X0,X1)
% 0.98/1.00      | r2_hidden(X0,X1)
% 0.98/1.00      | ~ l1_struct_0(sK2)
% 0.98/1.00      | k2_struct_0(sK2) != X1 ),
% 0.98/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_254]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_295,plain,
% 0.98/1.00      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
% 0.98/1.00      | r2_hidden(X0,k2_struct_0(sK2))
% 0.98/1.00      | ~ l1_struct_0(sK2) ),
% 0.98/1.00      inference(unflattening,[status(thm)],[c_294]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_497,plain,
% 0.98/1.00      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
% 0.98/1.00      | r2_hidden(X0,k2_struct_0(sK2)) ),
% 0.98/1.00      inference(backward_subsumption_resolution,
% 0.98/1.00                [status(thm)],
% 0.98/1.00                [c_484,c_295]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_737,plain,
% 0.98/1.00      ( ~ m1_subset_1(X0_51,k2_struct_0(sK2))
% 0.98/1.00      | r2_hidden(X0_51,k2_struct_0(sK2)) ),
% 0.98/1.00      inference(subtyping,[status(esa)],[c_497]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_945,plain,
% 0.98/1.00      ( m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
% 0.98/1.00      | r2_hidden(X0_51,k2_struct_0(sK2)) = iProver_top ),
% 0.98/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_989,plain,
% 0.98/1.00      ( r1_orders_2(sK1,X0_51,X1_51) != iProver_top
% 0.98/1.00      | r1_orders_2(sK2,X0_51,X1_51) = iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
% 0.98/1.00      | m1_subset_1(X1_51,k2_struct_0(sK1)) != iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
% 0.98/1.00      | m1_subset_1(X1_51,k2_struct_0(sK2)) != iProver_top ),
% 0.98/1.00      inference(forward_subsumption_resolution,
% 0.98/1.00                [status(thm)],
% 0.98/1.00                [c_981,c_945]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_1439,plain,
% 0.98/1.00      ( r1_orders_2(sK1,sK5,X0_51) != iProver_top
% 0.98/1.00      | r1_orders_2(sK2,sK5,X0_51) = iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
% 0.98/1.00      | m1_subset_1(sK5,k2_struct_0(sK2)) != iProver_top ),
% 0.98/1.00      inference(superposition,[status(thm)],[c_968,c_989]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_15,negated_conjecture,
% 0.98/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.98/1.00      inference(cnf_transformation,[],[f53]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_742,negated_conjecture,
% 0.98/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 0.98/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_940,plain,
% 0.98/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 0.98/1.00      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_962,plain,
% 0.98/1.00      ( m1_subset_1(sK5,k2_struct_0(sK2)) = iProver_top ),
% 0.98/1.00      inference(light_normalisation,[status(thm)],[c_940,c_734]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_1613,plain,
% 0.98/1.00      ( m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
% 0.98/1.00      | r1_orders_2(sK2,sK5,X0_51) = iProver_top
% 0.98/1.00      | r1_orders_2(sK1,sK5,X0_51) != iProver_top ),
% 0.98/1.00      inference(global_propositional_subsumption,
% 0.98/1.00                [status(thm)],
% 0.98/1.00                [c_1439,c_962]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_1614,plain,
% 0.98/1.00      ( r1_orders_2(sK1,sK5,X0_51) != iProver_top
% 0.98/1.00      | r1_orders_2(sK2,sK5,X0_51) = iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK1)) != iProver_top
% 0.98/1.00      | m1_subset_1(X0_51,k2_struct_0(sK2)) != iProver_top ),
% 0.98/1.00      inference(renaming,[status(thm)],[c_1613]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_1623,plain,
% 0.98/1.00      ( r1_orders_2(sK1,sK5,sK6) != iProver_top
% 0.98/1.00      | r1_orders_2(sK2,sK5,sK6) = iProver_top
% 0.98/1.00      | m1_subset_1(sK6,k2_struct_0(sK2)) != iProver_top ),
% 0.98/1.00      inference(superposition,[status(thm)],[c_965,c_1614]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_14,negated_conjecture,
% 0.98/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 0.98/1.00      inference(cnf_transformation,[],[f54]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_743,negated_conjecture,
% 0.98/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 0.98/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_939,plain,
% 0.98/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 0.98/1.00      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_959,plain,
% 0.98/1.00      ( m1_subset_1(sK6,k2_struct_0(sK2)) = iProver_top ),
% 0.98/1.00      inference(light_normalisation,[status(thm)],[c_939,c_734]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_11,negated_conjecture,
% 0.98/1.00      ( r1_orders_2(sK1,sK3,sK4) ),
% 0.98/1.00      inference(cnf_transformation,[],[f57]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_746,negated_conjecture,
% 0.98/1.00      ( r1_orders_2(sK1,sK3,sK4) ),
% 0.98/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_938,plain,
% 0.98/1.00      ( r1_orders_2(sK1,sK3,sK4) = iProver_top ),
% 0.98/1.00      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_956,plain,
% 0.98/1.00      ( r1_orders_2(sK1,sK5,sK6) = iProver_top ),
% 0.98/1.00      inference(light_normalisation,[status(thm)],[c_938,c_744,c_745]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_10,negated_conjecture,
% 0.98/1.00      ( ~ r1_orders_2(sK2,sK5,sK6) ),
% 0.98/1.00      inference(cnf_transformation,[],[f58]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(c_35,plain,
% 0.98/1.00      ( r1_orders_2(sK2,sK5,sK6) != iProver_top ),
% 0.98/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.98/1.00  
% 0.98/1.00  cnf(contradiction,plain,
% 0.98/1.00      ( $false ),
% 0.98/1.00      inference(minisat,[status(thm)],[c_1623,c_959,c_956,c_35]) ).
% 0.98/1.00  
% 0.98/1.00  
% 0.98/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.98/1.00  
% 0.98/1.00  ------                               Statistics
% 0.98/1.00  
% 0.98/1.00  ------ General
% 0.98/1.00  
% 0.98/1.00  abstr_ref_over_cycles:                  0
% 0.98/1.00  abstr_ref_under_cycles:                 0
% 0.98/1.00  gc_basic_clause_elim:                   0
% 0.98/1.00  forced_gc_time:                         0
% 0.98/1.00  parsing_time:                           0.008
% 0.98/1.00  unif_index_cands_time:                  0.
% 0.98/1.00  unif_index_add_time:                    0.
% 0.98/1.00  orderings_time:                         0.
% 0.98/1.00  out_proof_time:                         0.011
% 0.98/1.00  total_time:                             0.075
% 0.98/1.00  num_of_symbols:                         52
% 0.98/1.00  num_of_terms:                           1099
% 0.98/1.00  
% 0.98/1.00  ------ Preprocessing
% 0.98/1.00  
% 0.98/1.00  num_of_splits:                          0
% 0.98/1.00  num_of_split_atoms:                     0
% 0.98/1.00  num_of_reused_defs:                     0
% 0.98/1.00  num_eq_ax_congr_red:                    12
% 0.98/1.00  num_of_sem_filtered_clauses:            1
% 0.98/1.00  num_of_subtypes:                        3
% 0.98/1.00  monotx_restored_types:                  0
% 0.98/1.00  sat_num_of_epr_types:                   0
% 0.98/1.00  sat_num_of_non_cyclic_types:            0
% 0.98/1.00  sat_guarded_non_collapsed_types:        0
% 0.98/1.00  num_pure_diseq_elim:                    0
% 0.98/1.00  simp_replaced_by:                       0
% 0.98/1.00  res_preprocessed:                       81
% 0.98/1.00  prep_upred:                             0
% 0.98/1.00  prep_unflattend:                        32
% 0.98/1.00  smt_new_axioms:                         0
% 0.98/1.00  pred_elim_cands:                        3
% 0.98/1.00  pred_elim:                              9
% 0.98/1.00  pred_elim_cl:                           10
% 0.98/1.00  pred_elim_cycles:                       13
% 0.98/1.00  merged_defs:                            0
% 0.98/1.00  merged_defs_ncl:                        0
% 0.98/1.00  bin_hyper_res:                          0
% 0.98/1.00  prep_cycles:                            4
% 0.98/1.00  pred_elim_time:                         0.008
% 0.98/1.00  splitting_time:                         0.
% 0.98/1.00  sem_filter_time:                        0.
% 0.98/1.00  monotx_time:                            0.
% 0.98/1.00  subtype_inf_time:                       0.
% 0.98/1.00  
% 0.98/1.00  ------ Problem properties
% 0.98/1.00  
% 0.98/1.00  clauses:                                14
% 0.98/1.00  conjectures:                            8
% 0.98/1.00  epr:                                    4
% 0.98/1.00  horn:                                   14
% 0.98/1.00  ground:                                 11
% 0.98/1.00  unary:                                  11
% 0.98/1.00  binary:                                 2
% 0.98/1.00  lits:                                   22
% 0.98/1.00  lits_eq:                                5
% 0.98/1.00  fd_pure:                                0
% 0.98/1.00  fd_pseudo:                              0
% 0.98/1.00  fd_cond:                                0
% 0.98/1.00  fd_pseudo_cond:                         0
% 0.98/1.00  ac_symbols:                             0
% 0.98/1.00  
% 0.98/1.00  ------ Propositional Solver
% 0.98/1.00  
% 0.98/1.00  prop_solver_calls:                      27
% 0.98/1.00  prop_fast_solver_calls:                 492
% 0.98/1.00  smt_solver_calls:                       0
% 0.98/1.00  smt_fast_solver_calls:                  0
% 0.98/1.00  prop_num_of_clauses:                    459
% 0.98/1.00  prop_preprocess_simplified:             1983
% 0.98/1.00  prop_fo_subsumed:                       18
% 0.98/1.00  prop_solver_time:                       0.
% 0.98/1.00  smt_solver_time:                        0.
% 0.98/1.00  smt_fast_solver_time:                   0.
% 0.98/1.00  prop_fast_solver_time:                  0.
% 0.98/1.00  prop_unsat_core_time:                   0.
% 0.98/1.00  
% 0.98/1.00  ------ QBF
% 0.98/1.00  
% 0.98/1.00  qbf_q_res:                              0
% 0.98/1.00  qbf_num_tautologies:                    0
% 0.98/1.00  qbf_prep_cycles:                        0
% 0.98/1.00  
% 0.98/1.00  ------ BMC1
% 0.98/1.00  
% 0.98/1.00  bmc1_current_bound:                     -1
% 0.98/1.00  bmc1_last_solved_bound:                 -1
% 0.98/1.00  bmc1_unsat_core_size:                   -1
% 0.98/1.00  bmc1_unsat_core_parents_size:           -1
% 0.98/1.00  bmc1_merge_next_fun:                    0
% 0.98/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.98/1.00  
% 0.98/1.00  ------ Instantiation
% 0.98/1.00  
% 0.98/1.00  inst_num_of_clauses:                    126
% 0.98/1.00  inst_num_in_passive:                    0
% 0.98/1.00  inst_num_in_active:                     98
% 0.98/1.00  inst_num_in_unprocessed:                28
% 0.98/1.00  inst_num_of_loops:                      110
% 0.98/1.00  inst_num_of_learning_restarts:          0
% 0.98/1.00  inst_num_moves_active_passive:          8
% 0.98/1.00  inst_lit_activity:                      0
% 0.98/1.00  inst_lit_activity_moves:                0
% 0.98/1.00  inst_num_tautologies:                   0
% 0.98/1.00  inst_num_prop_implied:                  0
% 0.98/1.00  inst_num_existing_simplified:           0
% 0.98/1.00  inst_num_eq_res_simplified:             0
% 0.98/1.00  inst_num_child_elim:                    0
% 0.98/1.00  inst_num_of_dismatching_blockings:      8
% 0.98/1.00  inst_num_of_non_proper_insts:           114
% 0.98/1.00  inst_num_of_duplicates:                 0
% 0.98/1.00  inst_inst_num_from_inst_to_res:         0
% 0.98/1.00  inst_dismatching_checking_time:         0.
% 0.98/1.00  
% 0.98/1.00  ------ Resolution
% 0.98/1.00  
% 0.98/1.00  res_num_of_clauses:                     0
% 0.98/1.00  res_num_in_passive:                     0
% 0.98/1.00  res_num_in_active:                      0
% 0.98/1.00  res_num_of_loops:                       85
% 0.98/1.00  res_forward_subset_subsumed:            35
% 0.98/1.00  res_backward_subset_subsumed:           0
% 0.98/1.00  res_forward_subsumed:                   0
% 0.98/1.00  res_backward_subsumed:                  0
% 0.98/1.00  res_forward_subsumption_resolution:     0
% 0.98/1.00  res_backward_subsumption_resolution:    2
% 0.98/1.00  res_clause_to_clause_subsumption:       36
% 0.98/1.00  res_orphan_elimination:                 0
% 0.98/1.00  res_tautology_del:                      18
% 0.98/1.00  res_num_eq_res_simplified:              0
% 0.98/1.00  res_num_sel_changes:                    0
% 0.98/1.00  res_moves_from_active_to_pass:          0
% 0.98/1.00  
% 0.98/1.00  ------ Superposition
% 0.98/1.00  
% 0.98/1.00  sup_time_total:                         0.
% 0.98/1.00  sup_time_generating:                    0.
% 0.98/1.00  sup_time_sim_full:                      0.
% 0.98/1.00  sup_time_sim_immed:                     0.
% 0.98/1.00  
% 0.98/1.00  sup_num_of_clauses:                     23
% 0.98/1.00  sup_num_in_active:                      22
% 0.98/1.00  sup_num_in_passive:                     1
% 0.98/1.00  sup_num_of_loops:                       21
% 0.98/1.00  sup_fw_superposition:                   10
% 0.98/1.00  sup_bw_superposition:                   0
% 0.98/1.00  sup_immediate_simplified:               0
% 0.98/1.00  sup_given_eliminated:                   0
% 0.98/1.00  comparisons_done:                       0
% 0.98/1.00  comparisons_avoided:                    0
% 0.98/1.00  
% 0.98/1.00  ------ Simplifications
% 0.98/1.00  
% 0.98/1.00  
% 0.98/1.00  sim_fw_subset_subsumed:                 0
% 0.98/1.00  sim_bw_subset_subsumed:                 0
% 0.98/1.00  sim_fw_subsumed:                        0
% 0.98/1.00  sim_bw_subsumed:                        0
% 0.98/1.00  sim_fw_subsumption_res:                 1
% 0.98/1.00  sim_bw_subsumption_res:                 0
% 0.98/1.00  sim_tautology_del:                      0
% 0.98/1.00  sim_eq_tautology_del:                   0
% 0.98/1.00  sim_eq_res_simp:                        0
% 0.98/1.00  sim_fw_demodulated:                     0
% 0.98/1.00  sim_bw_demodulated:                     0
% 0.98/1.00  sim_light_normalised:                   6
% 0.98/1.00  sim_joinable_taut:                      0
% 0.98/1.00  sim_joinable_simp:                      0
% 0.98/1.00  sim_ac_normalised:                      0
% 0.98/1.00  sim_smt_subsumption:                    0
% 0.98/1.00  
%------------------------------------------------------------------------------
