%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:04 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 391 expanded)
%              Number of clauses        :   71 (  86 expanded)
%              Number of leaves         :   22 ( 170 expanded)
%              Depth                    :   23
%              Number of atoms          :  573 (3666 expanded)
%              Number of equality atoms :  102 ( 788 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X3,X4)
          & r1_orders_2(X2,X5,X6)
          & X4 = X6
          & X3 = X5
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_orders_2(X1,X3,X4)
        & r1_orders_2(X2,X5,sK9)
        & sK9 = X4
        & X3 = X5
        & m1_subset_1(sK9,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
            & r1_orders_2(X2,sK8,X6)
            & X4 = X6
            & sK8 = X3
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
                ( ~ r1_orders_2(X1,X3,sK7)
                & r1_orders_2(X2,X5,X6)
                & sK7 = X6
                & X3 = X5
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
                    ( ~ r1_orders_2(X1,sK6,X4)
                    & r1_orders_2(X2,X5,X6)
                    & X4 = X6
                    & sK6 = X5
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                        & r1_orders_2(sK5,X5,X6)
                        & X4 = X6
                        & X3 = X5
                        & m1_subset_1(X6,u1_struct_0(sK5)) )
                    & m1_subset_1(X5,u1_struct_0(sK5)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & m1_yellow_6(sK5,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
                            ( ~ r1_orders_2(sK4,X3,X4)
                            & r1_orders_2(X2,X5,X6)
                            & X4 = X6
                            & X3 = X5
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(sK4)) )
                & m1_subset_1(X3,u1_struct_0(sK4)) )
            & m1_yellow_6(X2,X0,sK4) )
        & l1_waybel_0(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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
              & m1_yellow_6(X2,sK3,X1) )
          & l1_waybel_0(X1,sK3) )
      & l1_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ r1_orders_2(sK4,sK6,sK7)
    & r1_orders_2(sK5,sK8,sK9)
    & sK7 = sK9
    & sK6 = sK8
    & m1_subset_1(sK9,u1_struct_0(sK5))
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_yellow_6(sK5,sK3,sK4)
    & l1_waybel_0(sK4,sK3)
    & l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f24,f43,f42,f41,f40,f39,f38,f37])).

fof(f67,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    m1_yellow_6(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    r1_orders_2(sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    sK6 = sK8 ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
              <=> ( u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2))
                  & m1_yellow_0(X2,X1) ) )
              | ~ l1_waybel_0(X2,X0) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_yellow_0(X2,X1)
      | ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK2(X0,X5),X0)
        & r2_hidden(X5,sK2(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(X2,sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK0(X0,X1),X3) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK0(X0,X1),X4) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK0(X0,X1),X3) )
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( ( r2_hidden(sK1(X0,X1),X0)
              & r2_hidden(sK0(X0,X1),sK1(X0,X1)) )
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK2(X0,X5),X0)
                & r2_hidden(X5,sK2(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f47])).

fof(f2,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ~ r1_orders_2(sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_663,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_orders_2(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_664,plain,
    ( ~ l1_waybel_0(X0,sK3)
    | l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_30,negated_conjecture,
    ( m1_yellow_6(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_21,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_629,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_630,plain,
    ( ~ m1_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | l1_waybel_0(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_699,plain,
    ( ~ l1_waybel_0(X0,sK3)
    | l1_waybel_0(X1,sK3)
    | sK3 != sK3
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_630])).

cnf(c_700,plain,
    ( l1_waybel_0(sK5,sK3)
    | ~ l1_waybel_0(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_31,negated_conjecture,
    ( l1_waybel_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_702,plain,
    ( l1_waybel_0(sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_31])).

cnf(c_741,plain,
    ( l1_orders_2(X0)
    | sK3 != sK3
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_664,c_702])).

cnf(c_742,plain,
    ( l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( r1_orders_2(sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(k4_tarski(X0,X2),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | sK9 != X2
    | sK8 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_441,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | r2_hidden(k4_tarski(sK8,sK9),u1_orders_2(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_443,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),u1_orders_2(sK5))
    | ~ l1_orders_2(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_441,c_27,c_26])).

cnf(c_753,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),u1_orders_2(sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_742,c_443])).

cnf(c_1326,plain,
    ( r2_hidden(k4_tarski(sK8,sK9),u1_orders_2(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_24,negated_conjecture,
    ( sK7 = sK9 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,negated_conjecture,
    ( sK6 = sK8 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1359,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1326,c_24,c_25])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_191,plain,
    ( ~ l1_orders_2(X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ m1_yellow_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_16])).

cnf(c_192,plain,
    ( ~ m1_yellow_0(X0,X1)
    | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_20,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X0,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_173,plain,
    ( ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X0,X1,X2)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_21])).

cnf(c_174,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | ~ l1_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_614,plain,
    ( ~ m1_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | m1_yellow_0(X0,X2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_174,c_32])).

cnf(c_615,plain,
    ( ~ m1_yellow_6(X0,sK3,X1)
    | ~ l1_waybel_0(X1,sK3)
    | m1_yellow_0(X0,X1) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_710,plain,
    ( ~ l1_waybel_0(X0,sK3)
    | m1_yellow_0(X1,X0)
    | sK3 != sK3
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_615])).

cnf(c_711,plain,
    ( ~ l1_waybel_0(sK4,sK3)
    | m1_yellow_0(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_710])).

cnf(c_713,plain,
    ( m1_yellow_0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_711,c_31])).

cnf(c_759,plain,
    ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_192,c_713])).

cnf(c_760,plain,
    ( r1_tarski(u1_orders_2(sK5),u1_orders_2(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_666,plain,
    ( ~ l1_waybel_0(sK4,sK3)
    | l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_762,plain,
    ( r1_tarski(u1_orders_2(sK5),u1_orders_2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_31,c_666])).

cnf(c_788,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | u1_orders_2(sK5) != X0
    | u1_orders_2(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_762])).

cnf(c_789,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(u1_orders_2(sK4))) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_1325,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(u1_orders_2(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_1328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_2430,plain,
    ( r2_hidden(u1_orders_2(sK5),k1_zfmisc_1(u1_orders_2(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1328])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1335,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8342,plain,
    ( r2_hidden(X0,u1_orders_2(sK5)) != iProver_top
    | r2_hidden(X0,k3_tarski(k1_zfmisc_1(u1_orders_2(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2430,c_1335])).

cnf(c_6,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8343,plain,
    ( r2_hidden(X0,u1_orders_2(sK5)) != iProver_top
    | r2_hidden(X0,u1_orders_2(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8342,c_6])).

cnf(c_8720,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_8343])).

cnf(c_665,plain,
    ( l1_waybel_0(X0,sK3) != iProver_top
    | l1_orders_2(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_667,plain,
    ( l1_waybel_0(sK4,sK3) != iProver_top
    | l1_orders_2(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( ~ r1_orders_2(sK4,sK6,sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | sK7 != X2
    | sK6 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_429,plain,
    ( ~ r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_29,c_28])).

cnf(c_431,plain,
    ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_34,plain,
    ( l1_waybel_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8720,c_667,c_431,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 16:45:05 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 2.97/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.00  
% 2.97/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.00  
% 2.97/1.00  ------  iProver source info
% 2.97/1.00  
% 2.97/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.00  git: non_committed_changes: false
% 2.97/1.00  git: last_make_outside_of_git: false
% 2.97/1.00  
% 2.97/1.00  ------ 
% 2.97/1.00  
% 2.97/1.00  ------ Input Options
% 2.97/1.00  
% 2.97/1.00  --out_options                           all
% 2.97/1.00  --tptp_safe_out                         true
% 2.97/1.00  --problem_path                          ""
% 2.97/1.00  --include_path                          ""
% 2.97/1.00  --clausifier                            res/vclausify_rel
% 2.97/1.00  --clausifier_options                    --mode clausify
% 2.97/1.00  --stdin                                 false
% 2.97/1.00  --stats_out                             all
% 2.97/1.00  
% 2.97/1.00  ------ General Options
% 2.97/1.00  
% 2.97/1.00  --fof                                   false
% 2.97/1.00  --time_out_real                         305.
% 2.97/1.00  --time_out_virtual                      -1.
% 2.97/1.00  --symbol_type_check                     false
% 2.97/1.00  --clausify_out                          false
% 2.97/1.00  --sig_cnt_out                           false
% 2.97/1.00  --trig_cnt_out                          false
% 2.97/1.00  --trig_cnt_out_tolerance                1.
% 2.97/1.00  --trig_cnt_out_sk_spl                   false
% 2.97/1.00  --abstr_cl_out                          false
% 2.97/1.00  
% 2.97/1.00  ------ Global Options
% 2.97/1.00  
% 2.97/1.00  --schedule                              default
% 2.97/1.00  --add_important_lit                     false
% 2.97/1.00  --prop_solver_per_cl                    1000
% 2.97/1.00  --min_unsat_core                        false
% 2.97/1.00  --soft_assumptions                      false
% 2.97/1.00  --soft_lemma_size                       3
% 2.97/1.00  --prop_impl_unit_size                   0
% 2.97/1.00  --prop_impl_unit                        []
% 2.97/1.00  --share_sel_clauses                     true
% 2.97/1.00  --reset_solvers                         false
% 2.97/1.00  --bc_imp_inh                            [conj_cone]
% 2.97/1.00  --conj_cone_tolerance                   3.
% 2.97/1.00  --extra_neg_conj                        none
% 2.97/1.00  --large_theory_mode                     true
% 2.97/1.00  --prolific_symb_bound                   200
% 2.97/1.00  --lt_threshold                          2000
% 2.97/1.00  --clause_weak_htbl                      true
% 2.97/1.00  --gc_record_bc_elim                     false
% 2.97/1.00  
% 2.97/1.00  ------ Preprocessing Options
% 2.97/1.00  
% 2.97/1.00  --preprocessing_flag                    true
% 2.97/1.00  --time_out_prep_mult                    0.1
% 2.97/1.00  --splitting_mode                        input
% 2.97/1.00  --splitting_grd                         true
% 2.97/1.00  --splitting_cvd                         false
% 2.97/1.00  --splitting_cvd_svl                     false
% 2.97/1.00  --splitting_nvd                         32
% 2.97/1.00  --sub_typing                            true
% 2.97/1.00  --prep_gs_sim                           true
% 2.97/1.00  --prep_unflatten                        true
% 2.97/1.00  --prep_res_sim                          true
% 2.97/1.00  --prep_upred                            true
% 2.97/1.00  --prep_sem_filter                       exhaustive
% 2.97/1.00  --prep_sem_filter_out                   false
% 2.97/1.00  --pred_elim                             true
% 2.97/1.00  --res_sim_input                         true
% 2.97/1.00  --eq_ax_congr_red                       true
% 2.97/1.00  --pure_diseq_elim                       true
% 2.97/1.00  --brand_transform                       false
% 2.97/1.00  --non_eq_to_eq                          false
% 2.97/1.00  --prep_def_merge                        true
% 2.97/1.00  --prep_def_merge_prop_impl              false
% 2.97/1.01  --prep_def_merge_mbd                    true
% 2.97/1.01  --prep_def_merge_tr_red                 false
% 2.97/1.01  --prep_def_merge_tr_cl                  false
% 2.97/1.01  --smt_preprocessing                     true
% 2.97/1.01  --smt_ac_axioms                         fast
% 2.97/1.01  --preprocessed_out                      false
% 2.97/1.01  --preprocessed_stats                    false
% 2.97/1.01  
% 2.97/1.01  ------ Abstraction refinement Options
% 2.97/1.01  
% 2.97/1.01  --abstr_ref                             []
% 2.97/1.01  --abstr_ref_prep                        false
% 2.97/1.01  --abstr_ref_until_sat                   false
% 2.97/1.01  --abstr_ref_sig_restrict                funpre
% 2.97/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.01  --abstr_ref_under                       []
% 2.97/1.01  
% 2.97/1.01  ------ SAT Options
% 2.97/1.01  
% 2.97/1.01  --sat_mode                              false
% 2.97/1.01  --sat_fm_restart_options                ""
% 2.97/1.01  --sat_gr_def                            false
% 2.97/1.01  --sat_epr_types                         true
% 2.97/1.01  --sat_non_cyclic_types                  false
% 2.97/1.01  --sat_finite_models                     false
% 2.97/1.01  --sat_fm_lemmas                         false
% 2.97/1.01  --sat_fm_prep                           false
% 2.97/1.01  --sat_fm_uc_incr                        true
% 2.97/1.01  --sat_out_model                         small
% 2.97/1.01  --sat_out_clauses                       false
% 2.97/1.01  
% 2.97/1.01  ------ QBF Options
% 2.97/1.01  
% 2.97/1.01  --qbf_mode                              false
% 2.97/1.01  --qbf_elim_univ                         false
% 2.97/1.01  --qbf_dom_inst                          none
% 2.97/1.01  --qbf_dom_pre_inst                      false
% 2.97/1.01  --qbf_sk_in                             false
% 2.97/1.01  --qbf_pred_elim                         true
% 2.97/1.01  --qbf_split                             512
% 2.97/1.01  
% 2.97/1.01  ------ BMC1 Options
% 2.97/1.01  
% 2.97/1.01  --bmc1_incremental                      false
% 2.97/1.01  --bmc1_axioms                           reachable_all
% 2.97/1.01  --bmc1_min_bound                        0
% 2.97/1.01  --bmc1_max_bound                        -1
% 2.97/1.01  --bmc1_max_bound_default                -1
% 2.97/1.01  --bmc1_symbol_reachability              true
% 2.97/1.01  --bmc1_property_lemmas                  false
% 2.97/1.01  --bmc1_k_induction                      false
% 2.97/1.01  --bmc1_non_equiv_states                 false
% 2.97/1.01  --bmc1_deadlock                         false
% 2.97/1.01  --bmc1_ucm                              false
% 2.97/1.01  --bmc1_add_unsat_core                   none
% 2.97/1.01  --bmc1_unsat_core_children              false
% 2.97/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.01  --bmc1_out_stat                         full
% 2.97/1.01  --bmc1_ground_init                      false
% 2.97/1.01  --bmc1_pre_inst_next_state              false
% 2.97/1.01  --bmc1_pre_inst_state                   false
% 2.97/1.01  --bmc1_pre_inst_reach_state             false
% 2.97/1.01  --bmc1_out_unsat_core                   false
% 2.97/1.01  --bmc1_aig_witness_out                  false
% 2.97/1.01  --bmc1_verbose                          false
% 2.97/1.01  --bmc1_dump_clauses_tptp                false
% 2.97/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.01  --bmc1_dump_file                        -
% 2.97/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.01  --bmc1_ucm_extend_mode                  1
% 2.97/1.01  --bmc1_ucm_init_mode                    2
% 2.97/1.01  --bmc1_ucm_cone_mode                    none
% 2.97/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.01  --bmc1_ucm_relax_model                  4
% 2.97/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.01  --bmc1_ucm_layered_model                none
% 2.97/1.01  --bmc1_ucm_max_lemma_size               10
% 2.97/1.01  
% 2.97/1.01  ------ AIG Options
% 2.97/1.01  
% 2.97/1.01  --aig_mode                              false
% 2.97/1.01  
% 2.97/1.01  ------ Instantiation Options
% 2.97/1.01  
% 2.97/1.01  --instantiation_flag                    true
% 2.97/1.01  --inst_sos_flag                         false
% 2.97/1.01  --inst_sos_phase                        true
% 2.97/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel_side                     num_symb
% 2.97/1.01  --inst_solver_per_active                1400
% 2.97/1.01  --inst_solver_calls_frac                1.
% 2.97/1.01  --inst_passive_queue_type               priority_queues
% 2.97/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.01  --inst_passive_queues_freq              [25;2]
% 2.97/1.01  --inst_dismatching                      true
% 2.97/1.01  --inst_eager_unprocessed_to_passive     true
% 2.97/1.01  --inst_prop_sim_given                   true
% 2.97/1.01  --inst_prop_sim_new                     false
% 2.97/1.01  --inst_subs_new                         false
% 2.97/1.01  --inst_eq_res_simp                      false
% 2.97/1.01  --inst_subs_given                       false
% 2.97/1.01  --inst_orphan_elimination               true
% 2.97/1.01  --inst_learning_loop_flag               true
% 2.97/1.01  --inst_learning_start                   3000
% 2.97/1.01  --inst_learning_factor                  2
% 2.97/1.01  --inst_start_prop_sim_after_learn       3
% 2.97/1.01  --inst_sel_renew                        solver
% 2.97/1.01  --inst_lit_activity_flag                true
% 2.97/1.01  --inst_restr_to_given                   false
% 2.97/1.01  --inst_activity_threshold               500
% 2.97/1.01  --inst_out_proof                        true
% 2.97/1.01  
% 2.97/1.01  ------ Resolution Options
% 2.97/1.01  
% 2.97/1.01  --resolution_flag                       true
% 2.97/1.01  --res_lit_sel                           adaptive
% 2.97/1.01  --res_lit_sel_side                      none
% 2.97/1.01  --res_ordering                          kbo
% 2.97/1.01  --res_to_prop_solver                    active
% 2.97/1.01  --res_prop_simpl_new                    false
% 2.97/1.01  --res_prop_simpl_given                  true
% 2.97/1.01  --res_passive_queue_type                priority_queues
% 2.97/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.01  --res_passive_queues_freq               [15;5]
% 2.97/1.01  --res_forward_subs                      full
% 2.97/1.01  --res_backward_subs                     full
% 2.97/1.01  --res_forward_subs_resolution           true
% 2.97/1.01  --res_backward_subs_resolution          true
% 2.97/1.01  --res_orphan_elimination                true
% 2.97/1.01  --res_time_limit                        2.
% 2.97/1.01  --res_out_proof                         true
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Options
% 2.97/1.01  
% 2.97/1.01  --superposition_flag                    true
% 2.97/1.01  --sup_passive_queue_type                priority_queues
% 2.97/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.01  --demod_completeness_check              fast
% 2.97/1.01  --demod_use_ground                      true
% 2.97/1.01  --sup_to_prop_solver                    passive
% 2.97/1.01  --sup_prop_simpl_new                    true
% 2.97/1.01  --sup_prop_simpl_given                  true
% 2.97/1.01  --sup_fun_splitting                     false
% 2.97/1.01  --sup_smt_interval                      50000
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Simplification Setup
% 2.97/1.01  
% 2.97/1.01  --sup_indices_passive                   []
% 2.97/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_full_bw                           [BwDemod]
% 2.97/1.01  --sup_immed_triv                        [TrivRules]
% 2.97/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_immed_bw_main                     []
% 2.97/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  
% 2.97/1.01  ------ Combination Options
% 2.97/1.01  
% 2.97/1.01  --comb_res_mult                         3
% 2.97/1.01  --comb_sup_mult                         2
% 2.97/1.01  --comb_inst_mult                        10
% 2.97/1.01  
% 2.97/1.01  ------ Debug Options
% 2.97/1.01  
% 2.97/1.01  --dbg_backtrace                         false
% 2.97/1.01  --dbg_dump_prop_clauses                 false
% 2.97/1.01  --dbg_dump_prop_clauses_file            -
% 2.97/1.01  --dbg_out_stat                          false
% 2.97/1.01  ------ Parsing...
% 2.97/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.01  ------ Proving...
% 2.97/1.01  ------ Problem Properties 
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  clauses                                 20
% 2.97/1.01  conjectures                             6
% 2.97/1.01  EPR                                     3
% 2.97/1.01  Horn                                    18
% 2.97/1.01  unary                                   12
% 2.97/1.01  binary                                  3
% 2.97/1.01  lits                                    34
% 2.97/1.01  lits eq                                 10
% 2.97/1.01  fd_pure                                 0
% 2.97/1.01  fd_pseudo                               0
% 2.97/1.01  fd_cond                                 0
% 2.97/1.01  fd_pseudo_cond                          3
% 2.97/1.01  AC symbols                              0
% 2.97/1.01  
% 2.97/1.01  ------ Schedule dynamic 5 is on 
% 2.97/1.01  
% 2.97/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  ------ 
% 2.97/1.01  Current options:
% 2.97/1.01  ------ 
% 2.97/1.01  
% 2.97/1.01  ------ Input Options
% 2.97/1.01  
% 2.97/1.01  --out_options                           all
% 2.97/1.01  --tptp_safe_out                         true
% 2.97/1.01  --problem_path                          ""
% 2.97/1.01  --include_path                          ""
% 2.97/1.01  --clausifier                            res/vclausify_rel
% 2.97/1.01  --clausifier_options                    --mode clausify
% 2.97/1.01  --stdin                                 false
% 2.97/1.01  --stats_out                             all
% 2.97/1.01  
% 2.97/1.01  ------ General Options
% 2.97/1.01  
% 2.97/1.01  --fof                                   false
% 2.97/1.01  --time_out_real                         305.
% 2.97/1.01  --time_out_virtual                      -1.
% 2.97/1.01  --symbol_type_check                     false
% 2.97/1.01  --clausify_out                          false
% 2.97/1.01  --sig_cnt_out                           false
% 2.97/1.01  --trig_cnt_out                          false
% 2.97/1.01  --trig_cnt_out_tolerance                1.
% 2.97/1.01  --trig_cnt_out_sk_spl                   false
% 2.97/1.01  --abstr_cl_out                          false
% 2.97/1.01  
% 2.97/1.01  ------ Global Options
% 2.97/1.01  
% 2.97/1.01  --schedule                              default
% 2.97/1.01  --add_important_lit                     false
% 2.97/1.01  --prop_solver_per_cl                    1000
% 2.97/1.01  --min_unsat_core                        false
% 2.97/1.01  --soft_assumptions                      false
% 2.97/1.01  --soft_lemma_size                       3
% 2.97/1.01  --prop_impl_unit_size                   0
% 2.97/1.01  --prop_impl_unit                        []
% 2.97/1.01  --share_sel_clauses                     true
% 2.97/1.01  --reset_solvers                         false
% 2.97/1.01  --bc_imp_inh                            [conj_cone]
% 2.97/1.01  --conj_cone_tolerance                   3.
% 2.97/1.01  --extra_neg_conj                        none
% 2.97/1.01  --large_theory_mode                     true
% 2.97/1.01  --prolific_symb_bound                   200
% 2.97/1.01  --lt_threshold                          2000
% 2.97/1.01  --clause_weak_htbl                      true
% 2.97/1.01  --gc_record_bc_elim                     false
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing Options
% 2.97/1.01  
% 2.97/1.01  --preprocessing_flag                    true
% 2.97/1.01  --time_out_prep_mult                    0.1
% 2.97/1.01  --splitting_mode                        input
% 2.97/1.01  --splitting_grd                         true
% 2.97/1.01  --splitting_cvd                         false
% 2.97/1.01  --splitting_cvd_svl                     false
% 2.97/1.01  --splitting_nvd                         32
% 2.97/1.01  --sub_typing                            true
% 2.97/1.01  --prep_gs_sim                           true
% 2.97/1.01  --prep_unflatten                        true
% 2.97/1.01  --prep_res_sim                          true
% 2.97/1.01  --prep_upred                            true
% 2.97/1.01  --prep_sem_filter                       exhaustive
% 2.97/1.01  --prep_sem_filter_out                   false
% 2.97/1.01  --pred_elim                             true
% 2.97/1.01  --res_sim_input                         true
% 2.97/1.01  --eq_ax_congr_red                       true
% 2.97/1.01  --pure_diseq_elim                       true
% 2.97/1.01  --brand_transform                       false
% 2.97/1.01  --non_eq_to_eq                          false
% 2.97/1.01  --prep_def_merge                        true
% 2.97/1.01  --prep_def_merge_prop_impl              false
% 2.97/1.01  --prep_def_merge_mbd                    true
% 2.97/1.01  --prep_def_merge_tr_red                 false
% 2.97/1.01  --prep_def_merge_tr_cl                  false
% 2.97/1.01  --smt_preprocessing                     true
% 2.97/1.01  --smt_ac_axioms                         fast
% 2.97/1.01  --preprocessed_out                      false
% 2.97/1.01  --preprocessed_stats                    false
% 2.97/1.01  
% 2.97/1.01  ------ Abstraction refinement Options
% 2.97/1.01  
% 2.97/1.01  --abstr_ref                             []
% 2.97/1.01  --abstr_ref_prep                        false
% 2.97/1.01  --abstr_ref_until_sat                   false
% 2.97/1.01  --abstr_ref_sig_restrict                funpre
% 2.97/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.01  --abstr_ref_under                       []
% 2.97/1.01  
% 2.97/1.01  ------ SAT Options
% 2.97/1.01  
% 2.97/1.01  --sat_mode                              false
% 2.97/1.01  --sat_fm_restart_options                ""
% 2.97/1.01  --sat_gr_def                            false
% 2.97/1.01  --sat_epr_types                         true
% 2.97/1.01  --sat_non_cyclic_types                  false
% 2.97/1.01  --sat_finite_models                     false
% 2.97/1.01  --sat_fm_lemmas                         false
% 2.97/1.01  --sat_fm_prep                           false
% 2.97/1.01  --sat_fm_uc_incr                        true
% 2.97/1.01  --sat_out_model                         small
% 2.97/1.01  --sat_out_clauses                       false
% 2.97/1.01  
% 2.97/1.01  ------ QBF Options
% 2.97/1.01  
% 2.97/1.01  --qbf_mode                              false
% 2.97/1.01  --qbf_elim_univ                         false
% 2.97/1.01  --qbf_dom_inst                          none
% 2.97/1.01  --qbf_dom_pre_inst                      false
% 2.97/1.01  --qbf_sk_in                             false
% 2.97/1.01  --qbf_pred_elim                         true
% 2.97/1.01  --qbf_split                             512
% 2.97/1.01  
% 2.97/1.01  ------ BMC1 Options
% 2.97/1.01  
% 2.97/1.01  --bmc1_incremental                      false
% 2.97/1.01  --bmc1_axioms                           reachable_all
% 2.97/1.01  --bmc1_min_bound                        0
% 2.97/1.01  --bmc1_max_bound                        -1
% 2.97/1.01  --bmc1_max_bound_default                -1
% 2.97/1.01  --bmc1_symbol_reachability              true
% 2.97/1.01  --bmc1_property_lemmas                  false
% 2.97/1.01  --bmc1_k_induction                      false
% 2.97/1.01  --bmc1_non_equiv_states                 false
% 2.97/1.01  --bmc1_deadlock                         false
% 2.97/1.01  --bmc1_ucm                              false
% 2.97/1.01  --bmc1_add_unsat_core                   none
% 2.97/1.01  --bmc1_unsat_core_children              false
% 2.97/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.01  --bmc1_out_stat                         full
% 2.97/1.01  --bmc1_ground_init                      false
% 2.97/1.01  --bmc1_pre_inst_next_state              false
% 2.97/1.01  --bmc1_pre_inst_state                   false
% 2.97/1.01  --bmc1_pre_inst_reach_state             false
% 2.97/1.01  --bmc1_out_unsat_core                   false
% 2.97/1.01  --bmc1_aig_witness_out                  false
% 2.97/1.01  --bmc1_verbose                          false
% 2.97/1.01  --bmc1_dump_clauses_tptp                false
% 2.97/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.01  --bmc1_dump_file                        -
% 2.97/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.01  --bmc1_ucm_extend_mode                  1
% 2.97/1.01  --bmc1_ucm_init_mode                    2
% 2.97/1.01  --bmc1_ucm_cone_mode                    none
% 2.97/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.01  --bmc1_ucm_relax_model                  4
% 2.97/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.01  --bmc1_ucm_layered_model                none
% 2.97/1.01  --bmc1_ucm_max_lemma_size               10
% 2.97/1.01  
% 2.97/1.01  ------ AIG Options
% 2.97/1.01  
% 2.97/1.01  --aig_mode                              false
% 2.97/1.01  
% 2.97/1.01  ------ Instantiation Options
% 2.97/1.01  
% 2.97/1.01  --instantiation_flag                    true
% 2.97/1.01  --inst_sos_flag                         false
% 2.97/1.01  --inst_sos_phase                        true
% 2.97/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel_side                     none
% 2.97/1.01  --inst_solver_per_active                1400
% 2.97/1.01  --inst_solver_calls_frac                1.
% 2.97/1.01  --inst_passive_queue_type               priority_queues
% 2.97/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.01  --inst_passive_queues_freq              [25;2]
% 2.97/1.01  --inst_dismatching                      true
% 2.97/1.01  --inst_eager_unprocessed_to_passive     true
% 2.97/1.01  --inst_prop_sim_given                   true
% 2.97/1.01  --inst_prop_sim_new                     false
% 2.97/1.01  --inst_subs_new                         false
% 2.97/1.01  --inst_eq_res_simp                      false
% 2.97/1.01  --inst_subs_given                       false
% 2.97/1.01  --inst_orphan_elimination               true
% 2.97/1.01  --inst_learning_loop_flag               true
% 2.97/1.01  --inst_learning_start                   3000
% 2.97/1.01  --inst_learning_factor                  2
% 2.97/1.01  --inst_start_prop_sim_after_learn       3
% 2.97/1.01  --inst_sel_renew                        solver
% 2.97/1.01  --inst_lit_activity_flag                true
% 2.97/1.01  --inst_restr_to_given                   false
% 2.97/1.01  --inst_activity_threshold               500
% 2.97/1.01  --inst_out_proof                        true
% 2.97/1.01  
% 2.97/1.01  ------ Resolution Options
% 2.97/1.01  
% 2.97/1.01  --resolution_flag                       false
% 2.97/1.01  --res_lit_sel                           adaptive
% 2.97/1.01  --res_lit_sel_side                      none
% 2.97/1.01  --res_ordering                          kbo
% 2.97/1.01  --res_to_prop_solver                    active
% 2.97/1.01  --res_prop_simpl_new                    false
% 2.97/1.01  --res_prop_simpl_given                  true
% 2.97/1.01  --res_passive_queue_type                priority_queues
% 2.97/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.01  --res_passive_queues_freq               [15;5]
% 2.97/1.01  --res_forward_subs                      full
% 2.97/1.01  --res_backward_subs                     full
% 2.97/1.01  --res_forward_subs_resolution           true
% 2.97/1.01  --res_backward_subs_resolution          true
% 2.97/1.01  --res_orphan_elimination                true
% 2.97/1.01  --res_time_limit                        2.
% 2.97/1.01  --res_out_proof                         true
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Options
% 2.97/1.01  
% 2.97/1.01  --superposition_flag                    true
% 2.97/1.01  --sup_passive_queue_type                priority_queues
% 2.97/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.01  --demod_completeness_check              fast
% 2.97/1.01  --demod_use_ground                      true
% 2.97/1.01  --sup_to_prop_solver                    passive
% 2.97/1.01  --sup_prop_simpl_new                    true
% 2.97/1.01  --sup_prop_simpl_given                  true
% 2.97/1.01  --sup_fun_splitting                     false
% 2.97/1.01  --sup_smt_interval                      50000
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Simplification Setup
% 2.97/1.01  
% 2.97/1.01  --sup_indices_passive                   []
% 2.97/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_full_bw                           [BwDemod]
% 2.97/1.01  --sup_immed_triv                        [TrivRules]
% 2.97/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_immed_bw_main                     []
% 2.97/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  
% 2.97/1.01  ------ Combination Options
% 2.97/1.01  
% 2.97/1.01  --comb_res_mult                         3
% 2.97/1.01  --comb_sup_mult                         2
% 2.97/1.01  --comb_inst_mult                        10
% 2.97/1.01  
% 2.97/1.01  ------ Debug Options
% 2.97/1.01  
% 2.97/1.01  --dbg_backtrace                         false
% 2.97/1.01  --dbg_dump_prop_clauses                 false
% 2.97/1.01  --dbg_dump_prop_clauses_file            -
% 2.97/1.01  --dbg_out_stat                          false
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  ------ Proving...
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  % SZS status Theorem for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  fof(f9,axiom,(
% 2.97/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f19,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f9])).
% 2.97/1.01  
% 2.97/1.01  fof(f62,plain,(
% 2.97/1.01    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f19])).
% 2.97/1.01  
% 2.97/1.01  fof(f12,conjecture,(
% 2.97/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f13,negated_conjecture,(
% 2.97/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5) => r1_orders_2(X1,X3,X4)))))))))),
% 2.97/1.01    inference(negated_conjecture,[],[f12])).
% 2.97/1.01  
% 2.97/1.01  fof(f23,plain,(
% 2.97/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X1,X3,X4) & (r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f13])).
% 2.97/1.01  
% 2.97/1.01  fof(f24,plain,(
% 2.97/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0))),
% 2.97/1.01    inference(flattening,[],[f23])).
% 2.97/1.01  
% 2.97/1.01  fof(f43,plain,(
% 2.97/1.01    ( ! [X4,X2,X5,X3,X1] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,sK9) & sK9 = X4 & X3 = X5 & m1_subset_1(sK9,u1_struct_0(X2)))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f42,plain,(
% 2.97/1.01    ( ! [X4,X2,X3,X1] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) => (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,sK8,X6) & X4 = X6 & sK8 = X3 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f41,plain,(
% 2.97/1.01    ( ! [X2,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,sK7) & r1_orders_2(X2,X5,X6) & sK7 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f40,plain,(
% 2.97/1.01    ( ! [X2,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,sK6,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & sK6 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f39,plain,(
% 2.97/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(sK5,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(sK5,X0,X1))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f38,plain,(
% 2.97/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(sK4,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(sK4))) & m1_yellow_6(X2,X0,sK4)) & l1_waybel_0(sK4,X0))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f37,plain,(
% 2.97/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X3,X4) & r1_orders_2(X2,X5,X6) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,sK3,X1)) & l1_waybel_0(X1,sK3)) & l1_struct_0(sK3))),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f44,plain,(
% 2.97/1.01    ((((((~r1_orders_2(sK4,sK6,sK7) & r1_orders_2(sK5,sK8,sK9) & sK7 = sK9 & sK6 = sK8 & m1_subset_1(sK9,u1_struct_0(sK5))) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_yellow_6(sK5,sK3,sK4)) & l1_waybel_0(sK4,sK3)) & l1_struct_0(sK3)),
% 2.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f24,f43,f42,f41,f40,f39,f38,f37])).
% 2.97/1.01  
% 2.97/1.01  fof(f67,plain,(
% 2.97/1.01    l1_struct_0(sK3)),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f69,plain,(
% 2.97/1.01    m1_yellow_6(sK5,sK3,sK4)),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f11,axiom,(
% 2.97/1.01    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f21,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 2.97/1.01    inference(ennf_transformation,[],[f11])).
% 2.97/1.01  
% 2.97/1.01  fof(f22,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 2.97/1.01    inference(flattening,[],[f21])).
% 2.97/1.01  
% 2.97/1.01  fof(f66,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f22])).
% 2.97/1.01  
% 2.97/1.01  fof(f68,plain,(
% 2.97/1.01    l1_waybel_0(sK4,sK3)),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f6,axiom,(
% 2.97/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f16,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f6])).
% 2.97/1.01  
% 2.97/1.01  fof(f32,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.97/1.01    inference(nnf_transformation,[],[f16])).
% 2.97/1.01  
% 2.97/1.01  fof(f56,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f32])).
% 2.97/1.01  
% 2.97/1.01  fof(f76,plain,(
% 2.97/1.01    r1_orders_2(sK5,sK8,sK9)),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f72,plain,(
% 2.97/1.01    m1_subset_1(sK8,u1_struct_0(sK5))),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f73,plain,(
% 2.97/1.01    m1_subset_1(sK9,u1_struct_0(sK5))),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f75,plain,(
% 2.97/1.01    sK7 = sK9),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f74,plain,(
% 2.97/1.01    sK6 = sK8),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f5,axiom,(
% 2.97/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f31,plain,(
% 2.97/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.97/1.01    inference(nnf_transformation,[],[f5])).
% 2.97/1.01  
% 2.97/1.01  fof(f55,plain,(
% 2.97/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f31])).
% 2.97/1.01  
% 2.97/1.01  fof(f7,axiom,(
% 2.97/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f17,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f7])).
% 2.97/1.01  
% 2.97/1.01  fof(f33,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.97/1.01    inference(nnf_transformation,[],[f17])).
% 2.97/1.01  
% 2.97/1.01  fof(f34,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 2.97/1.01    inference(flattening,[],[f33])).
% 2.97/1.01  
% 2.97/1.01  fof(f59,plain,(
% 2.97/1.01    ( ! [X0,X1] : (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f34])).
% 2.97/1.01  
% 2.97/1.01  fof(f8,axiom,(
% 2.97/1.01    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => l1_orders_2(X1)))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f18,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f8])).
% 2.97/1.01  
% 2.97/1.01  fof(f61,plain,(
% 2.97/1.01    ( ! [X0,X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f18])).
% 2.97/1.01  
% 2.97/1.01  fof(f10,axiom,(
% 2.97/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (l1_waybel_0(X2,X0) => (m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f20,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_yellow_6(X2,X0,X1) <=> (u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f10])).
% 2.97/1.01  
% 2.97/1.01  fof(f35,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | (u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1))) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 2.97/1.01    inference(nnf_transformation,[],[f20])).
% 2.97/1.01  
% 2.97/1.01  fof(f36,plain,(
% 2.97/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_yellow_6(X2,X0,X1) | u1_waybel_0(X0,X2) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) | ~m1_yellow_0(X2,X1)) & ((u1_waybel_0(X0,X2) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X2)) & m1_yellow_0(X2,X1)) | ~m1_yellow_6(X2,X0,X1))) | ~l1_waybel_0(X2,X0)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 2.97/1.01    inference(flattening,[],[f35])).
% 2.97/1.01  
% 2.97/1.01  fof(f63,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (m1_yellow_0(X2,X1) | ~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X2,X0) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f36])).
% 2.97/1.01  
% 2.97/1.01  fof(f3,axiom,(
% 2.97/1.01    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f52,plain,(
% 2.97/1.01    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.97/1.01    inference(cnf_transformation,[],[f3])).
% 2.97/1.01  
% 2.97/1.01  fof(f4,axiom,(
% 2.97/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f14,plain,(
% 2.97/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.97/1.01    inference(ennf_transformation,[],[f4])).
% 2.97/1.01  
% 2.97/1.01  fof(f15,plain,(
% 2.97/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.97/1.01    inference(flattening,[],[f14])).
% 2.97/1.01  
% 2.97/1.01  fof(f53,plain,(
% 2.97/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f15])).
% 2.97/1.01  
% 2.97/1.01  fof(f1,axiom,(
% 2.97/1.01    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f25,plain,(
% 2.97/1.01    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 2.97/1.01    inference(nnf_transformation,[],[f1])).
% 2.97/1.01  
% 2.97/1.01  fof(f26,plain,(
% 2.97/1.01    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.97/1.01    inference(rectify,[],[f25])).
% 2.97/1.01  
% 2.97/1.01  fof(f29,plain,(
% 2.97/1.01    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK2(X0,X5),X0) & r2_hidden(X5,sK2(X0,X5))))),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f28,plain,(
% 2.97/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK1(X0,X1),X0) & r2_hidden(X2,sK1(X0,X1))))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f27,plain,(
% 2.97/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK0(X0,X1),X3)) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK0(X0,X1),X4)) | r2_hidden(sK0(X0,X1),X1))))),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f30,plain,(
% 2.97/1.01    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK0(X0,X1),X3)) | ~r2_hidden(sK0(X0,X1),X1)) & ((r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK0(X0,X1),sK1(X0,X1))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK2(X0,X5),X0) & r2_hidden(X5,sK2(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 2.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 2.97/1.01  
% 2.97/1.01  fof(f47,plain,(
% 2.97/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 2.97/1.01    inference(cnf_transformation,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  fof(f78,plain,(
% 2.97/1.01    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 2.97/1.01    inference(equality_resolution,[],[f47])).
% 2.97/1.01  
% 2.97/1.01  fof(f2,axiom,(
% 2.97/1.01    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f51,plain,(
% 2.97/1.01    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.97/1.01    inference(cnf_transformation,[],[f2])).
% 2.97/1.01  
% 2.97/1.01  fof(f57,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f32])).
% 2.97/1.01  
% 2.97/1.01  fof(f77,plain,(
% 2.97/1.01    ~r1_orders_2(sK4,sK6,sK7)),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f70,plain,(
% 2.97/1.01    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  fof(f71,plain,(
% 2.97/1.01    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.97/1.01    inference(cnf_transformation,[],[f44])).
% 2.97/1.01  
% 2.97/1.01  cnf(c_17,plain,
% 2.97/1.01      ( ~ l1_waybel_0(X0,X1) | ~ l1_struct_0(X1) | l1_orders_2(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_32,negated_conjecture,
% 2.97/1.01      ( l1_struct_0(sK3) ),
% 2.97/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_663,plain,
% 2.97/1.01      ( ~ l1_waybel_0(X0,X1) | l1_orders_2(X0) | sK3 != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_664,plain,
% 2.97/1.01      ( ~ l1_waybel_0(X0,sK3) | l1_orders_2(X0) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_663]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_30,negated_conjecture,
% 2.97/1.01      ( m1_yellow_6(sK5,sK3,sK4) ),
% 2.97/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_21,plain,
% 2.97/1.01      ( ~ m1_yellow_6(X0,X1,X2)
% 2.97/1.01      | ~ l1_waybel_0(X2,X1)
% 2.97/1.01      | l1_waybel_0(X0,X1)
% 2.97/1.01      | ~ l1_struct_0(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_629,plain,
% 2.97/1.01      ( ~ m1_yellow_6(X0,X1,X2)
% 2.97/1.01      | ~ l1_waybel_0(X2,X1)
% 2.97/1.01      | l1_waybel_0(X0,X1)
% 2.97/1.01      | sK3 != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_630,plain,
% 2.97/1.01      ( ~ m1_yellow_6(X0,sK3,X1)
% 2.97/1.01      | ~ l1_waybel_0(X1,sK3)
% 2.97/1.01      | l1_waybel_0(X0,sK3) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_629]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_699,plain,
% 2.97/1.01      ( ~ l1_waybel_0(X0,sK3)
% 2.97/1.01      | l1_waybel_0(X1,sK3)
% 2.97/1.01      | sK3 != sK3
% 2.97/1.01      | sK5 != X1
% 2.97/1.01      | sK4 != X0 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_630]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_700,plain,
% 2.97/1.01      ( l1_waybel_0(sK5,sK3) | ~ l1_waybel_0(sK4,sK3) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_699]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_31,negated_conjecture,
% 2.97/1.01      ( l1_waybel_0(sK4,sK3) ),
% 2.97/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_702,plain,
% 2.97/1.01      ( l1_waybel_0(sK5,sK3) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_700,c_31]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_741,plain,
% 2.97/1.01      ( l1_orders_2(X0) | sK3 != sK3 | sK5 != X0 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_664,c_702]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_742,plain,
% 2.97/1.01      ( l1_orders_2(sK5) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_741]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_12,plain,
% 2.97/1.01      ( ~ r1_orders_2(X0,X1,X2)
% 2.97/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.01      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 2.97/1.01      | ~ l1_orders_2(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_23,negated_conjecture,
% 2.97/1.01      ( r1_orders_2(sK5,sK8,sK9) ),
% 2.97/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_440,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.01      | r2_hidden(k4_tarski(X0,X2),u1_orders_2(X1))
% 2.97/1.01      | ~ l1_orders_2(X1)
% 2.97/1.01      | sK9 != X2
% 2.97/1.01      | sK8 != X0
% 2.97/1.01      | sK5 != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_441,plain,
% 2.97/1.01      ( ~ m1_subset_1(sK9,u1_struct_0(sK5))
% 2.97/1.01      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.97/1.01      | r2_hidden(k4_tarski(sK8,sK9),u1_orders_2(sK5))
% 2.97/1.01      | ~ l1_orders_2(sK5) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_440]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_27,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_26,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_443,plain,
% 2.97/1.01      ( r2_hidden(k4_tarski(sK8,sK9),u1_orders_2(sK5))
% 2.97/1.01      | ~ l1_orders_2(sK5) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_441,c_27,c_26]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_753,plain,
% 2.97/1.01      ( r2_hidden(k4_tarski(sK8,sK9),u1_orders_2(sK5)) ),
% 2.97/1.01      inference(backward_subsumption_resolution,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_742,c_443]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1326,plain,
% 2.97/1.01      ( r2_hidden(k4_tarski(sK8,sK9),u1_orders_2(sK5)) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_24,negated_conjecture,
% 2.97/1.01      ( sK7 = sK9 ),
% 2.97/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_25,negated_conjecture,
% 2.97/1.01      ( sK6 = sK8 ),
% 2.97/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1359,plain,
% 2.97/1.01      ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK5)) = iProver_top ),
% 2.97/1.01      inference(light_normalisation,[status(thm)],[c_1326,c_24,c_25]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_9,plain,
% 2.97/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_244,plain,
% 2.97/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.97/1.01      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_14,plain,
% 2.97/1.01      ( ~ m1_yellow_0(X0,X1)
% 2.97/1.01      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.97/1.01      | ~ l1_orders_2(X1)
% 2.97/1.01      | ~ l1_orders_2(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_16,plain,
% 2.97/1.01      ( ~ m1_yellow_0(X0,X1) | ~ l1_orders_2(X1) | l1_orders_2(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_191,plain,
% 2.97/1.01      ( ~ l1_orders_2(X1)
% 2.97/1.01      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.97/1.01      | ~ m1_yellow_0(X0,X1) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_14,c_16]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_192,plain,
% 2.97/1.01      ( ~ m1_yellow_0(X0,X1)
% 2.97/1.01      | r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.97/1.01      | ~ l1_orders_2(X1) ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_191]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_20,plain,
% 2.97/1.01      ( ~ m1_yellow_6(X0,X1,X2)
% 2.97/1.01      | ~ l1_waybel_0(X2,X1)
% 2.97/1.01      | ~ l1_waybel_0(X0,X1)
% 2.97/1.01      | m1_yellow_0(X0,X2)
% 2.97/1.01      | ~ l1_struct_0(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_173,plain,
% 2.97/1.01      ( ~ l1_waybel_0(X2,X1)
% 2.97/1.01      | ~ m1_yellow_6(X0,X1,X2)
% 2.97/1.01      | m1_yellow_0(X0,X2)
% 2.97/1.01      | ~ l1_struct_0(X1) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_20,c_21]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_174,plain,
% 2.97/1.01      ( ~ m1_yellow_6(X0,X1,X2)
% 2.97/1.01      | ~ l1_waybel_0(X2,X1)
% 2.97/1.01      | m1_yellow_0(X0,X2)
% 2.97/1.01      | ~ l1_struct_0(X1) ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_173]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_614,plain,
% 2.97/1.01      ( ~ m1_yellow_6(X0,X1,X2)
% 2.97/1.01      | ~ l1_waybel_0(X2,X1)
% 2.97/1.01      | m1_yellow_0(X0,X2)
% 2.97/1.01      | sK3 != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_174,c_32]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_615,plain,
% 2.97/1.01      ( ~ m1_yellow_6(X0,sK3,X1)
% 2.97/1.01      | ~ l1_waybel_0(X1,sK3)
% 2.97/1.01      | m1_yellow_0(X0,X1) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_614]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_710,plain,
% 2.97/1.01      ( ~ l1_waybel_0(X0,sK3)
% 2.97/1.01      | m1_yellow_0(X1,X0)
% 2.97/1.01      | sK3 != sK3
% 2.97/1.01      | sK5 != X1
% 2.97/1.01      | sK4 != X0 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_615]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_711,plain,
% 2.97/1.01      ( ~ l1_waybel_0(sK4,sK3) | m1_yellow_0(sK5,sK4) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_710]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_713,plain,
% 2.97/1.01      ( m1_yellow_0(sK5,sK4) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_711,c_31]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_759,plain,
% 2.97/1.01      ( r1_tarski(u1_orders_2(X0),u1_orders_2(X1))
% 2.97/1.01      | ~ l1_orders_2(X1)
% 2.97/1.01      | sK5 != X0
% 2.97/1.01      | sK4 != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_192,c_713]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_760,plain,
% 2.97/1.01      ( r1_tarski(u1_orders_2(sK5),u1_orders_2(sK4))
% 2.97/1.01      | ~ l1_orders_2(sK4) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_759]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_666,plain,
% 2.97/1.01      ( ~ l1_waybel_0(sK4,sK3) | l1_orders_2(sK4) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_664]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_762,plain,
% 2.97/1.01      ( r1_tarski(u1_orders_2(sK5),u1_orders_2(sK4)) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_760,c_31,c_666]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_788,plain,
% 2.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.01      | u1_orders_2(sK5) != X0
% 2.97/1.01      | u1_orders_2(sK4) != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_244,c_762]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_789,plain,
% 2.97/1.01      ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(u1_orders_2(sK4))) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_788]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1325,plain,
% 2.97/1.01      ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(u1_orders_2(sK4))) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_7,plain,
% 2.97/1.01      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_8,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_410,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_411,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.01      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_410]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1328,plain,
% 2.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.97/1.01      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2430,plain,
% 2.97/1.01      ( r2_hidden(u1_orders_2(sK5),k1_zfmisc_1(u1_orders_2(sK4))) = iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_1325,c_1328]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3,plain,
% 2.97/1.01      ( ~ r2_hidden(X0,X1)
% 2.97/1.01      | ~ r2_hidden(X2,X0)
% 2.97/1.01      | r2_hidden(X2,k3_tarski(X1)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1335,plain,
% 2.97/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.97/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.97/1.01      | r2_hidden(X2,k3_tarski(X1)) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_8342,plain,
% 2.97/1.01      ( r2_hidden(X0,u1_orders_2(sK5)) != iProver_top
% 2.97/1.01      | r2_hidden(X0,k3_tarski(k1_zfmisc_1(u1_orders_2(sK4)))) = iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2430,c_1335]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_6,plain,
% 2.97/1.01      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 2.97/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_8343,plain,
% 2.97/1.01      ( r2_hidden(X0,u1_orders_2(sK5)) != iProver_top
% 2.97/1.01      | r2_hidden(X0,u1_orders_2(sK4)) = iProver_top ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_8342,c_6]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_8720,plain,
% 2.97/1.01      ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK4)) = iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_1359,c_8343]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_665,plain,
% 2.97/1.01      ( l1_waybel_0(X0,sK3) != iProver_top
% 2.97/1.01      | l1_orders_2(X0) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_667,plain,
% 2.97/1.01      ( l1_waybel_0(sK4,sK3) != iProver_top
% 2.97/1.01      | l1_orders_2(sK4) = iProver_top ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_665]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_11,plain,
% 2.97/1.01      ( r1_orders_2(X0,X1,X2)
% 2.97/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.97/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.97/1.01      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 2.97/1.01      | ~ l1_orders_2(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_22,negated_conjecture,
% 2.97/1.01      ( ~ r1_orders_2(sK4,sK6,sK7) ),
% 2.97/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_426,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.97/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.97/1.01      | ~ r2_hidden(k4_tarski(X0,X2),u1_orders_2(X1))
% 2.97/1.01      | ~ l1_orders_2(X1)
% 2.97/1.01      | sK7 != X2
% 2.97/1.01      | sK6 != X0
% 2.97/1.01      | sK4 != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_427,plain,
% 2.97/1.01      ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 2.97/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.97/1.01      | ~ r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK4))
% 2.97/1.01      | ~ l1_orders_2(sK4) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_426]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_29,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_28,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_429,plain,
% 2.97/1.01      ( ~ r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK4))
% 2.97/1.01      | ~ l1_orders_2(sK4) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_427,c_29,c_28]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_431,plain,
% 2.97/1.01      ( r2_hidden(k4_tarski(sK6,sK7),u1_orders_2(sK4)) != iProver_top
% 2.97/1.01      | l1_orders_2(sK4) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_34,plain,
% 2.97/1.01      ( l1_waybel_0(sK4,sK3) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(contradiction,plain,
% 2.97/1.01      ( $false ),
% 2.97/1.01      inference(minisat,[status(thm)],[c_8720,c_667,c_431,c_34]) ).
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  ------                               Statistics
% 2.97/1.01  
% 2.97/1.01  ------ General
% 2.97/1.01  
% 2.97/1.01  abstr_ref_over_cycles:                  0
% 2.97/1.01  abstr_ref_under_cycles:                 0
% 2.97/1.01  gc_basic_clause_elim:                   0
% 2.97/1.01  forced_gc_time:                         0
% 2.97/1.01  parsing_time:                           0.01
% 2.97/1.01  unif_index_cands_time:                  0.
% 2.97/1.01  unif_index_add_time:                    0.
% 2.97/1.01  orderings_time:                         0.
% 2.97/1.01  out_proof_time:                         0.009
% 2.97/1.01  total_time:                             0.256
% 2.97/1.01  num_of_symbols:                         58
% 2.97/1.01  num_of_terms:                           9897
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing
% 2.97/1.01  
% 2.97/1.01  num_of_splits:                          0
% 2.97/1.01  num_of_split_atoms:                     0
% 2.97/1.01  num_of_reused_defs:                     0
% 2.97/1.01  num_eq_ax_congr_red:                    27
% 2.97/1.01  num_of_sem_filtered_clauses:            1
% 2.97/1.01  num_of_subtypes:                        0
% 2.97/1.01  monotx_restored_types:                  0
% 2.97/1.01  sat_num_of_epr_types:                   0
% 2.97/1.01  sat_num_of_non_cyclic_types:            0
% 2.97/1.01  sat_guarded_non_collapsed_types:        0
% 2.97/1.01  num_pure_diseq_elim:                    0
% 2.97/1.01  simp_replaced_by:                       0
% 2.97/1.01  res_preprocessed:                       116
% 2.97/1.01  prep_upred:                             0
% 2.97/1.01  prep_unflattend:                        50
% 2.97/1.01  smt_new_axioms:                         0
% 2.97/1.01  pred_elim_cands:                        2
% 2.97/1.01  pred_elim:                              8
% 2.97/1.01  pred_elim_cl:                           13
% 2.97/1.01  pred_elim_cycles:                       11
% 2.97/1.01  merged_defs:                            2
% 2.97/1.01  merged_defs_ncl:                        0
% 2.97/1.01  bin_hyper_res:                          2
% 2.97/1.01  prep_cycles:                            4
% 2.97/1.01  pred_elim_time:                         0.009
% 2.97/1.01  splitting_time:                         0.
% 2.97/1.01  sem_filter_time:                        0.
% 2.97/1.01  monotx_time:                            0.
% 2.97/1.01  subtype_inf_time:                       0.
% 2.97/1.01  
% 2.97/1.01  ------ Problem properties
% 2.97/1.01  
% 2.97/1.01  clauses:                                20
% 2.97/1.01  conjectures:                            6
% 2.97/1.01  epr:                                    3
% 2.97/1.01  horn:                                   18
% 2.97/1.01  ground:                                 12
% 2.97/1.01  unary:                                  12
% 2.97/1.01  binary:                                 3
% 2.97/1.01  lits:                                   34
% 2.97/1.01  lits_eq:                                10
% 2.97/1.01  fd_pure:                                0
% 2.97/1.01  fd_pseudo:                              0
% 2.97/1.01  fd_cond:                                0
% 2.97/1.01  fd_pseudo_cond:                         3
% 2.97/1.01  ac_symbols:                             0
% 2.97/1.01  
% 2.97/1.01  ------ Propositional Solver
% 2.97/1.01  
% 2.97/1.01  prop_solver_calls:                      28
% 2.97/1.01  prop_fast_solver_calls:                 783
% 2.97/1.01  smt_solver_calls:                       0
% 2.97/1.01  smt_fast_solver_calls:                  0
% 2.97/1.01  prop_num_of_clauses:                    3104
% 2.97/1.01  prop_preprocess_simplified:             5964
% 2.97/1.01  prop_fo_subsumed:                       14
% 2.97/1.01  prop_solver_time:                       0.
% 2.97/1.01  smt_solver_time:                        0.
% 2.97/1.01  smt_fast_solver_time:                   0.
% 2.97/1.01  prop_fast_solver_time:                  0.
% 2.97/1.01  prop_unsat_core_time:                   0.
% 2.97/1.01  
% 2.97/1.01  ------ QBF
% 2.97/1.01  
% 2.97/1.01  qbf_q_res:                              0
% 2.97/1.01  qbf_num_tautologies:                    0
% 2.97/1.01  qbf_prep_cycles:                        0
% 2.97/1.01  
% 2.97/1.01  ------ BMC1
% 2.97/1.01  
% 2.97/1.01  bmc1_current_bound:                     -1
% 2.97/1.01  bmc1_last_solved_bound:                 -1
% 2.97/1.01  bmc1_unsat_core_size:                   -1
% 2.97/1.01  bmc1_unsat_core_parents_size:           -1
% 2.97/1.01  bmc1_merge_next_fun:                    0
% 2.97/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.01  
% 2.97/1.01  ------ Instantiation
% 2.97/1.01  
% 2.97/1.01  inst_num_of_clauses:                    653
% 2.97/1.01  inst_num_in_passive:                    292
% 2.97/1.01  inst_num_in_active:                     279
% 2.97/1.01  inst_num_in_unprocessed:                82
% 2.97/1.01  inst_num_of_loops:                      310
% 2.97/1.01  inst_num_of_learning_restarts:          0
% 2.97/1.01  inst_num_moves_active_passive:          28
% 2.97/1.01  inst_lit_activity:                      0
% 2.97/1.01  inst_lit_activity_moves:                0
% 2.97/1.01  inst_num_tautologies:                   0
% 2.97/1.01  inst_num_prop_implied:                  0
% 2.97/1.01  inst_num_existing_simplified:           0
% 2.97/1.01  inst_num_eq_res_simplified:             0
% 2.97/1.01  inst_num_child_elim:                    0
% 2.97/1.01  inst_num_of_dismatching_blockings:      97
% 2.97/1.01  inst_num_of_non_proper_insts:           537
% 2.97/1.01  inst_num_of_duplicates:                 0
% 2.97/1.01  inst_inst_num_from_inst_to_res:         0
% 2.97/1.01  inst_dismatching_checking_time:         0.
% 2.97/1.01  
% 2.97/1.01  ------ Resolution
% 2.97/1.01  
% 2.97/1.01  res_num_of_clauses:                     0
% 2.97/1.01  res_num_in_passive:                     0
% 2.97/1.01  res_num_in_active:                      0
% 2.97/1.01  res_num_of_loops:                       120
% 2.97/1.01  res_forward_subset_subsumed:            78
% 2.97/1.01  res_backward_subset_subsumed:           0
% 2.97/1.01  res_forward_subsumed:                   0
% 2.97/1.01  res_backward_subsumed:                  0
% 2.97/1.01  res_forward_subsumption_resolution:     0
% 2.97/1.01  res_backward_subsumption_resolution:    2
% 2.97/1.01  res_clause_to_clause_subsumption:       1741
% 2.97/1.01  res_orphan_elimination:                 0
% 2.97/1.01  res_tautology_del:                      53
% 2.97/1.01  res_num_eq_res_simplified:              0
% 2.97/1.01  res_num_sel_changes:                    0
% 2.97/1.01  res_moves_from_active_to_pass:          0
% 2.97/1.01  
% 2.97/1.01  ------ Superposition
% 2.97/1.01  
% 2.97/1.01  sup_time_total:                         0.
% 2.97/1.01  sup_time_generating:                    0.
% 2.97/1.01  sup_time_sim_full:                      0.
% 2.97/1.01  sup_time_sim_immed:                     0.
% 2.97/1.01  
% 2.97/1.01  sup_num_of_clauses:                     279
% 2.97/1.01  sup_num_in_active:                      61
% 2.97/1.01  sup_num_in_passive:                     218
% 2.97/1.01  sup_num_of_loops:                       60
% 2.97/1.01  sup_fw_superposition:                   143
% 2.97/1.01  sup_bw_superposition:                   155
% 2.97/1.01  sup_immediate_simplified:               30
% 2.97/1.01  sup_given_eliminated:                   0
% 2.97/1.01  comparisons_done:                       0
% 2.97/1.01  comparisons_avoided:                    0
% 2.97/1.01  
% 2.97/1.01  ------ Simplifications
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  sim_fw_subset_subsumed:                 5
% 2.97/1.01  sim_bw_subset_subsumed:                 0
% 2.97/1.01  sim_fw_subsumed:                        10
% 2.97/1.01  sim_bw_subsumed:                        2
% 2.97/1.01  sim_fw_subsumption_res:                 1
% 2.97/1.01  sim_bw_subsumption_res:                 0
% 2.97/1.01  sim_tautology_del:                      1
% 2.97/1.01  sim_eq_tautology_del:                   11
% 2.97/1.01  sim_eq_res_simp:                        4
% 2.97/1.01  sim_fw_demodulated:                     12
% 2.97/1.01  sim_bw_demodulated:                     0
% 2.97/1.01  sim_light_normalised:                   7
% 2.97/1.01  sim_joinable_taut:                      0
% 2.97/1.01  sim_joinable_simp:                      0
% 2.97/1.01  sim_ac_normalised:                      0
% 2.97/1.01  sim_smt_subsumption:                    0
% 2.97/1.01  
%------------------------------------------------------------------------------
