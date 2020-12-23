%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:12 EST 2020

% Result     : CounterSatisfiable 1.76s
% Output     : Saturation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  171 (1384 expanded)
%              Number of clauses        :  105 ( 293 expanded)
%              Number of leaves         :   26 ( 656 expanded)
%              Depth                    :   14
%              Number of atoms          :  821 (25345 expanded)
%              Number of equality atoms :  247 (3845 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   48 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( r2_yellow_0(X0,X2)
                 => r2_yellow_0(X1,X2) )
                & ( r1_yellow_0(X0,X2)
                 => r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X0,X2) )
              & ( r1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X0,X2) ) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( l1_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                 => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                           => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                             => ! [X6] :
                                  ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))
                                     => ( X6 = X7
                                       => ( ( r3_waybel_0(X0,X1,X4,X6)
                                           => r3_waybel_0(X2,X3,X5,X7) )
                                          & ( r4_waybel_0(X0,X1,X4,X6)
                                           => r4_waybel_0(X2,X3,X5,X7) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( l1_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                   => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(X5) )
                             => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                               => ! [X6] :
                                    ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
                                   => ! [X7] :
                                        ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))
                                       => ( X6 = X7
                                         => ( ( r3_waybel_0(X0,X1,X4,X6)
                                             => r3_waybel_0(X2,X3,X5,X7) )
                                            & ( r4_waybel_0(X0,X1,X4,X6)
                                             => r4_waybel_0(X2,X3,X5,X7) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                      & r3_waybel_0(X0,X1,X4,X6) )
                                    | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                      & r4_waybel_0(X0,X1,X4,X6) ) )
                                  & X6 = X7
                                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                  & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                  & l1_orders_2(X3)
                  & ~ v2_struct_0(X3) )
              & l1_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                      & r3_waybel_0(X0,X1,X4,X6) )
                                    | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                      & r4_waybel_0(X0,X1,X4,X6) ) )
                                  & X6 = X7
                                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                  & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                  & l1_orders_2(X3)
                  & ~ v2_struct_0(X3) )
              & l1_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
              & r3_waybel_0(X0,X1,X4,X6) )
            | ( ~ r4_waybel_0(X2,X3,X5,X7)
              & r4_waybel_0(X0,X1,X4,X6) ) )
          & X6 = X7
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ( ( ~ r3_waybel_0(X2,X3,X5,sK7)
            & r3_waybel_0(X0,X1,X4,X6) )
          | ( ~ r4_waybel_0(X2,X3,X5,sK7)
            & r4_waybel_0(X0,X1,X4,X6) ) )
        & sK7 = X6
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                  & r3_waybel_0(X0,X1,X4,X6) )
                | ( ~ r4_waybel_0(X2,X3,X5,X7)
                  & r4_waybel_0(X0,X1,X4,X6) ) )
              & X6 = X7
              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X7] :
            ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                & r3_waybel_0(X0,X1,X4,sK6) )
              | ( ~ r4_waybel_0(X2,X3,X5,X7)
                & r4_waybel_0(X0,X1,X4,sK6) ) )
            & sK6 = X7
            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                      & r3_waybel_0(X0,X1,X4,X6) )
                    | ( ~ r4_waybel_0(X2,X3,X5,X7)
                      & r4_waybel_0(X0,X1,X4,X6) ) )
                  & X6 = X7
                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
          & v1_funct_1(X5) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ( ( ~ r3_waybel_0(X2,X3,sK5,X7)
                    & r3_waybel_0(X0,X1,X4,X6) )
                  | ( ~ r4_waybel_0(X2,X3,sK5,X7)
                    & r4_waybel_0(X0,X1,X4,X6) ) )
                & X6 = X7
                & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X3))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                          & r3_waybel_0(X0,X1,X4,X6) )
                        | ( ~ r4_waybel_0(X2,X3,X5,X7)
                          & r4_waybel_0(X0,X1,X4,X6) ) )
                      & X6 = X7
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                  & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                        & r3_waybel_0(X0,X1,sK4,X6) )
                      | ( ~ r4_waybel_0(X2,X3,X5,X7)
                        & r4_waybel_0(X0,X1,sK4,X6) ) )
                    & X6 = X7
                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),sK4,X5)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                              & r3_waybel_0(X0,X1,X4,X6) )
                            | ( ~ r4_waybel_0(X2,X3,X5,X7)
                              & r4_waybel_0(X0,X1,X4,X6) ) )
                          & X6 = X7
                          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                      & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
          & l1_orders_2(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ( ~ r3_waybel_0(X2,sK3,X5,X7)
                            & r3_waybel_0(X0,X1,X4,X6) )
                          | ( ~ r4_waybel_0(X2,sK3,X5,X7)
                            & r4_waybel_0(X0,X1,X4,X6) ) )
                        & X6 = X7
                        & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                    & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(sK3),X4,X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
        & l1_orders_2(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                  & r3_waybel_0(X0,X1,X4,X6) )
                                | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                  & r4_waybel_0(X0,X1,X4,X6) ) )
                              & X6 = X7
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & l1_orders_2(X3)
              & ~ v2_struct_0(X3) )
          & l1_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ( ~ r3_waybel_0(sK2,X3,X5,X7)
                                & r3_waybel_0(X0,X1,X4,X6) )
                              | ( ~ r4_waybel_0(sK2,X3,X5,X7)
                                & r4_waybel_0(X0,X1,X4,X6) ) )
                            & X6 = X7
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2))) )
                        & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK2),u1_struct_0(X3),X4,X5)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
                    & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
            & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
            & l1_orders_2(X3)
            & ~ v2_struct_0(X3) )
        & l1_orders_2(sK2)
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
                              ( ? [X7] :
                                  ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                      & r3_waybel_0(X0,X1,X4,X6) )
                                    | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                      & r4_waybel_0(X0,X1,X4,X6) ) )
                                  & X6 = X7
                                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                  & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                  & l1_orders_2(X3)
                  & ~ v2_struct_0(X3) )
              & l1_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                    & r3_waybel_0(X0,sK1,X4,X6) )
                                  | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                    & r4_waybel_0(X0,sK1,X4,X6) ) )
                                & X6 = X7
                                & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & l1_orders_2(X3)
                & ~ v2_struct_0(X3) )
            & l1_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & l1_orders_2(sK1)
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
                                ( ? [X7] :
                                    ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                        & r3_waybel_0(X0,X1,X4,X6) )
                                      | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                        & r4_waybel_0(X0,X1,X4,X6) ) )
                                    & X6 = X7
                                    & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                                & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                    & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                    & l1_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                & l1_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ( ~ r3_waybel_0(X2,X3,X5,X7)
                                      & r3_waybel_0(sK0,X1,X4,X6) )
                                    | ( ~ r4_waybel_0(X2,X3,X5,X7)
                                      & r4_waybel_0(sK0,X1,X4,X6) ) )
                                  & X6 = X7
                                  & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) )
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
                          & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                  & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                  & l1_orders_2(X3)
                  & ~ v2_struct_0(X3) )
              & l1_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
        & r3_waybel_0(sK0,sK1,sK4,sK6) )
      | ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
        & r4_waybel_0(sK0,sK1,sK4,sK6) ) )
    & sK6 = sK7
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    & l1_orders_2(sK3)
    & ~ v2_struct_0(sK3)
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & l1_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f25,f34,f33,f32,f31,f30,f29,f28,f27])).

fof(f56,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_297,plain,
    ( ~ r4_waybel_0(X0,X1,X2,X3)
    | r4_waybel_0(X4,X5,X6,X7)
    | X6 != X2
    | X4 != X0
    | X5 != X1
    | X7 != X3 ),
    theory(equality)).

cnf(c_296,plain,
    ( ~ r3_waybel_0(X0,X1,X2,X3)
    | r3_waybel_0(X4,X5,X6,X7)
    | X6 != X2
    | X4 != X0
    | X5 != X1
    | X7 != X3 ),
    theory(equality)).

cnf(c_295,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_294,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X5 != X2
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_293,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | r1_funct_2(X6,X7,X8,X9,X10,X11)
    | X8 != X2
    | X6 != X0
    | X7 != X1
    | X9 != X3
    | X10 != X4
    | X11 != X5 ),
    theory(equality)).

cnf(c_287,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_286,plain,
    ( ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_285,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1051,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_8,plain,
    ( ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | k2_yellow_0(X2,X1) = k2_yellow_0(X0,X1)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | k1_yellow_0(X2,X1) = k1_yellow_0(X0,X1)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X2,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r2_yellow_0(X2,X1)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X2)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1230,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1837,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1230])).

cnf(c_2,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_410,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_31])).

cnf(c_411,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_412,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_1839,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK1) = X1
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1230])).

cnf(c_1971,plain,
    ( u1_orders_2(sK1) = X1
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1837,c_412,c_1839])).

cnf(c_1972,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK1) = X1 ),
    inference(renaming,[status(thm)],[c_1971])).

cnf(c_1978,plain,
    ( u1_orders_2(sK3) = u1_orders_2(sK1) ),
    inference(equality_resolution,[status(thm)],[c_1972])).

cnf(c_26,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1838,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1230])).

cnf(c_33,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_36,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_74,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_76,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_1840,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1230])).

cnf(c_2110,plain,
    ( u1_orders_2(sK0) = X1
    | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1838,c_36,c_76,c_1840])).

cnf(c_2111,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1 ),
    inference(renaming,[status(thm)],[c_2110])).

cnf(c_2115,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(superposition,[status(thm)],[c_25,c_2111])).

cnf(c_2554,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | u1_orders_2(sK0) = u1_orders_2(sK3) ),
    inference(demodulation,[status(thm)],[c_1978,c_2115])).

cnf(c_2117,plain,
    ( u1_orders_2(sK2) = u1_orders_2(sK0) ),
    inference(equality_resolution,[status(thm)],[c_2111])).

cnf(c_2887,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | u1_orders_2(sK2) = u1_orders_2(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2554,c_2117])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1229,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1776,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1229])).

cnf(c_75,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1778,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1229])).

cnf(c_1813,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1778])).

cnf(c_1952,plain,
    ( u1_struct_0(sK0) = X0
    | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1776,c_33,c_75,c_1813])).

cnf(c_1953,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(renaming,[status(thm)],[c_1952])).

cnf(c_1959,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK2) ),
    inference(equality_resolution,[status(thm)],[c_1953])).

cnf(c_1957,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_25,c_1953])).

cnf(c_1775,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1229])).

cnf(c_1777,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1229])).

cnf(c_1810,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1777])).

cnf(c_1879,plain,
    ( u1_struct_0(sK1) = X0
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1775,c_411,c_1810])).

cnf(c_1880,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(renaming,[status(thm)],[c_1879])).

cnf(c_1886,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK1) ),
    inference(equality_resolution,[status(thm)],[c_1880])).

cnf(c_2141,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | u1_struct_0(sK3) = u1_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1957,c_1886])).

cnf(c_2516,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | u1_struct_0(sK3) = u1_struct_0(sK2) ),
    inference(demodulation,[status(thm)],[c_1959,c_2141])).

cnf(c_2119,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1 ),
    inference(demodulation,[status(thm)],[c_2117,c_2111])).

cnf(c_1980,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK3) = X1 ),
    inference(demodulation,[status(thm)],[c_1978,c_1972])).

cnf(c_1961,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(demodulation,[status(thm)],[c_1959,c_1953])).

cnf(c_1888,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK3) = X0 ),
    inference(demodulation,[status(thm)],[c_1886,c_1880])).

cnf(c_11,negated_conjecture,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ r3_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,negated_conjecture,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | r3_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_463,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | sK6 != sK7
    | sK4 != sK5
    | sK1 != sK3
    | sK0 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_15,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_465,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | sK4 != sK5
    | sK1 != sK3
    | sK0 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_15])).

cnf(c_12,negated_conjecture,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r3_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,negated_conjecture,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | r3_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_432,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | sK6 != sK7
    | sK4 != sK5
    | sK1 != sK3
    | sK0 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_434,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | sK4 != sK5
    | sK1 != sK3
    | sK0 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_15])).

cnf(c_492,plain,
    ( sK6 != sK7
    | sK4 != sK5
    | sK1 != sK3
    | sK0 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_465,c_434])).

cnf(c_493,plain,
    ( sK4 != sK5
    | sK1 != sK3
    | sK0 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_15])).

cnf(c_10,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_509,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK3) != X5
    | u1_struct_0(sK2) != X4
    | sK4 != X0
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_510,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | sK5 = sK4 ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_27,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_326,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_0])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_344,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_326,c_28])).

cnf(c_345,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_366,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_326,c_32])).

cnf(c_367,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_512,plain,
    ( sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_31,c_27,c_24,c_23,c_22,c_21,c_20,c_19,c_345,c_367])).

cnf(c_1257,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | sK5 != sK5 ),
    inference(light_normalisation,[status(thm)],[c_493,c_512])).

cnf(c_1258,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1257])).

cnf(c_29,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_403,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_29])).

cnf(c_404,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_1223,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_396,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_27])).

cnf(c_397,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_1224,plain,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1228,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1226,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:59:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.76/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/0.98  
% 1.76/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.76/0.98  
% 1.76/0.98  ------  iProver source info
% 1.76/0.98  
% 1.76/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.76/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.76/0.98  git: non_committed_changes: false
% 1.76/0.98  git: last_make_outside_of_git: false
% 1.76/0.98  
% 1.76/0.98  ------ 
% 1.76/0.98  
% 1.76/0.98  ------ Input Options
% 1.76/0.98  
% 1.76/0.98  --out_options                           all
% 1.76/0.98  --tptp_safe_out                         true
% 1.76/0.98  --problem_path                          ""
% 1.76/0.98  --include_path                          ""
% 1.76/0.98  --clausifier                            res/vclausify_rel
% 1.76/0.98  --clausifier_options                    --mode clausify
% 1.76/0.98  --stdin                                 false
% 1.76/0.98  --stats_out                             all
% 1.76/0.98  
% 1.76/0.98  ------ General Options
% 1.76/0.98  
% 1.76/0.98  --fof                                   false
% 1.76/0.98  --time_out_real                         305.
% 1.76/0.98  --time_out_virtual                      -1.
% 1.76/0.98  --symbol_type_check                     false
% 1.76/0.98  --clausify_out                          false
% 1.76/0.98  --sig_cnt_out                           false
% 1.76/0.98  --trig_cnt_out                          false
% 1.76/0.98  --trig_cnt_out_tolerance                1.
% 1.76/0.98  --trig_cnt_out_sk_spl                   false
% 1.76/0.98  --abstr_cl_out                          false
% 1.76/0.98  
% 1.76/0.98  ------ Global Options
% 1.76/0.98  
% 1.76/0.98  --schedule                              default
% 1.76/0.98  --add_important_lit                     false
% 1.76/0.98  --prop_solver_per_cl                    1000
% 1.76/0.98  --min_unsat_core                        false
% 1.76/0.98  --soft_assumptions                      false
% 1.76/0.98  --soft_lemma_size                       3
% 1.76/0.98  --prop_impl_unit_size                   0
% 1.76/0.98  --prop_impl_unit                        []
% 1.76/0.98  --share_sel_clauses                     true
% 1.76/0.98  --reset_solvers                         false
% 1.76/0.98  --bc_imp_inh                            [conj_cone]
% 1.76/0.98  --conj_cone_tolerance                   3.
% 1.76/0.98  --extra_neg_conj                        none
% 1.76/0.98  --large_theory_mode                     true
% 1.76/0.98  --prolific_symb_bound                   200
% 1.76/0.98  --lt_threshold                          2000
% 1.76/0.98  --clause_weak_htbl                      true
% 1.76/0.98  --gc_record_bc_elim                     false
% 1.76/0.98  
% 1.76/0.98  ------ Preprocessing Options
% 1.76/0.98  
% 1.76/0.98  --preprocessing_flag                    true
% 1.76/0.98  --time_out_prep_mult                    0.1
% 1.76/0.98  --splitting_mode                        input
% 1.76/0.98  --splitting_grd                         true
% 1.76/0.98  --splitting_cvd                         false
% 1.76/0.98  --splitting_cvd_svl                     false
% 1.76/0.98  --splitting_nvd                         32
% 1.76/0.98  --sub_typing                            true
% 1.76/0.98  --prep_gs_sim                           true
% 1.76/0.98  --prep_unflatten                        true
% 1.76/0.98  --prep_res_sim                          true
% 1.76/0.98  --prep_upred                            true
% 1.76/0.98  --prep_sem_filter                       exhaustive
% 1.76/0.98  --prep_sem_filter_out                   false
% 1.76/0.98  --pred_elim                             true
% 1.76/0.98  --res_sim_input                         true
% 1.76/0.98  --eq_ax_congr_red                       true
% 1.76/0.98  --pure_diseq_elim                       true
% 1.76/0.98  --brand_transform                       false
% 1.76/0.98  --non_eq_to_eq                          false
% 1.76/0.98  --prep_def_merge                        true
% 1.76/0.98  --prep_def_merge_prop_impl              false
% 1.76/0.98  --prep_def_merge_mbd                    true
% 1.76/0.98  --prep_def_merge_tr_red                 false
% 1.76/0.98  --prep_def_merge_tr_cl                  false
% 1.76/0.98  --smt_preprocessing                     true
% 1.76/0.98  --smt_ac_axioms                         fast
% 1.76/0.98  --preprocessed_out                      false
% 1.76/0.98  --preprocessed_stats                    false
% 1.76/0.98  
% 1.76/0.98  ------ Abstraction refinement Options
% 1.76/0.98  
% 1.76/0.98  --abstr_ref                             []
% 1.76/0.98  --abstr_ref_prep                        false
% 1.76/0.98  --abstr_ref_until_sat                   false
% 1.76/0.98  --abstr_ref_sig_restrict                funpre
% 1.76/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/0.98  --abstr_ref_under                       []
% 1.76/0.98  
% 1.76/0.98  ------ SAT Options
% 1.76/0.98  
% 1.76/0.98  --sat_mode                              false
% 1.76/0.98  --sat_fm_restart_options                ""
% 1.76/0.98  --sat_gr_def                            false
% 1.76/0.98  --sat_epr_types                         true
% 1.76/0.98  --sat_non_cyclic_types                  false
% 1.76/0.98  --sat_finite_models                     false
% 1.76/0.98  --sat_fm_lemmas                         false
% 1.76/0.98  --sat_fm_prep                           false
% 1.76/0.98  --sat_fm_uc_incr                        true
% 1.76/0.98  --sat_out_model                         small
% 1.76/0.98  --sat_out_clauses                       false
% 1.76/0.98  
% 1.76/0.98  ------ QBF Options
% 1.76/0.98  
% 1.76/0.98  --qbf_mode                              false
% 1.76/0.98  --qbf_elim_univ                         false
% 1.76/0.98  --qbf_dom_inst                          none
% 1.76/0.98  --qbf_dom_pre_inst                      false
% 1.76/0.98  --qbf_sk_in                             false
% 1.76/0.98  --qbf_pred_elim                         true
% 1.76/0.98  --qbf_split                             512
% 1.76/0.98  
% 1.76/0.98  ------ BMC1 Options
% 1.76/0.98  
% 1.76/0.98  --bmc1_incremental                      false
% 1.76/0.98  --bmc1_axioms                           reachable_all
% 1.76/0.98  --bmc1_min_bound                        0
% 1.76/0.98  --bmc1_max_bound                        -1
% 1.76/0.98  --bmc1_max_bound_default                -1
% 1.76/0.98  --bmc1_symbol_reachability              true
% 1.76/0.98  --bmc1_property_lemmas                  false
% 1.76/0.98  --bmc1_k_induction                      false
% 1.76/0.98  --bmc1_non_equiv_states                 false
% 1.76/0.98  --bmc1_deadlock                         false
% 1.76/0.98  --bmc1_ucm                              false
% 1.76/0.98  --bmc1_add_unsat_core                   none
% 1.76/0.98  --bmc1_unsat_core_children              false
% 1.76/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/0.98  --bmc1_out_stat                         full
% 1.76/0.98  --bmc1_ground_init                      false
% 1.76/0.98  --bmc1_pre_inst_next_state              false
% 1.76/0.98  --bmc1_pre_inst_state                   false
% 1.76/0.98  --bmc1_pre_inst_reach_state             false
% 1.76/0.98  --bmc1_out_unsat_core                   false
% 1.76/0.98  --bmc1_aig_witness_out                  false
% 1.76/0.98  --bmc1_verbose                          false
% 1.76/0.98  --bmc1_dump_clauses_tptp                false
% 1.76/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.76/0.98  --bmc1_dump_file                        -
% 1.76/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.76/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.76/0.98  --bmc1_ucm_extend_mode                  1
% 1.76/0.98  --bmc1_ucm_init_mode                    2
% 1.76/0.98  --bmc1_ucm_cone_mode                    none
% 1.76/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.76/0.98  --bmc1_ucm_relax_model                  4
% 1.76/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.76/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/0.98  --bmc1_ucm_layered_model                none
% 1.76/0.98  --bmc1_ucm_max_lemma_size               10
% 1.76/0.98  
% 1.76/0.98  ------ AIG Options
% 1.76/0.98  
% 1.76/0.98  --aig_mode                              false
% 1.76/0.98  
% 1.76/0.98  ------ Instantiation Options
% 1.76/0.98  
% 1.76/0.98  --instantiation_flag                    true
% 1.76/0.98  --inst_sos_flag                         false
% 1.76/0.98  --inst_sos_phase                        true
% 1.76/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/0.98  --inst_lit_sel_side                     num_symb
% 1.76/0.98  --inst_solver_per_active                1400
% 1.76/0.98  --inst_solver_calls_frac                1.
% 1.76/0.98  --inst_passive_queue_type               priority_queues
% 1.76/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/0.98  --inst_passive_queues_freq              [25;2]
% 1.76/0.98  --inst_dismatching                      true
% 1.76/0.98  --inst_eager_unprocessed_to_passive     true
% 1.76/0.98  --inst_prop_sim_given                   true
% 1.76/0.98  --inst_prop_sim_new                     false
% 1.76/0.98  --inst_subs_new                         false
% 1.76/0.98  --inst_eq_res_simp                      false
% 1.76/0.98  --inst_subs_given                       false
% 1.76/0.98  --inst_orphan_elimination               true
% 1.76/0.98  --inst_learning_loop_flag               true
% 1.76/0.98  --inst_learning_start                   3000
% 1.76/0.98  --inst_learning_factor                  2
% 1.76/0.98  --inst_start_prop_sim_after_learn       3
% 1.76/0.98  --inst_sel_renew                        solver
% 1.76/0.98  --inst_lit_activity_flag                true
% 1.76/0.98  --inst_restr_to_given                   false
% 1.76/0.98  --inst_activity_threshold               500
% 1.76/0.98  --inst_out_proof                        true
% 1.76/0.98  
% 1.76/0.98  ------ Resolution Options
% 1.76/0.98  
% 1.76/0.98  --resolution_flag                       true
% 1.76/0.98  --res_lit_sel                           adaptive
% 1.76/0.98  --res_lit_sel_side                      none
% 1.76/0.98  --res_ordering                          kbo
% 1.76/0.98  --res_to_prop_solver                    active
% 1.76/0.98  --res_prop_simpl_new                    false
% 1.76/0.98  --res_prop_simpl_given                  true
% 1.76/0.98  --res_passive_queue_type                priority_queues
% 1.76/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/0.98  --res_passive_queues_freq               [15;5]
% 1.76/0.98  --res_forward_subs                      full
% 1.76/0.98  --res_backward_subs                     full
% 1.76/0.98  --res_forward_subs_resolution           true
% 1.76/0.98  --res_backward_subs_resolution          true
% 1.76/0.98  --res_orphan_elimination                true
% 1.76/0.98  --res_time_limit                        2.
% 1.76/0.98  --res_out_proof                         true
% 1.76/0.98  
% 1.76/0.98  ------ Superposition Options
% 1.76/0.98  
% 1.76/0.98  --superposition_flag                    true
% 1.76/0.98  --sup_passive_queue_type                priority_queues
% 1.76/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.76/0.98  --demod_completeness_check              fast
% 1.76/0.98  --demod_use_ground                      true
% 1.76/0.98  --sup_to_prop_solver                    passive
% 1.76/0.98  --sup_prop_simpl_new                    true
% 1.76/0.98  --sup_prop_simpl_given                  true
% 1.76/0.98  --sup_fun_splitting                     false
% 1.76/0.98  --sup_smt_interval                      50000
% 1.76/0.98  
% 1.76/0.98  ------ Superposition Simplification Setup
% 1.76/0.98  
% 1.76/0.98  --sup_indices_passive                   []
% 1.76/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.98  --sup_full_bw                           [BwDemod]
% 1.76/0.98  --sup_immed_triv                        [TrivRules]
% 1.76/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.98  --sup_immed_bw_main                     []
% 1.76/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.98  
% 1.76/0.98  ------ Combination Options
% 1.76/0.98  
% 1.76/0.98  --comb_res_mult                         3
% 1.76/0.98  --comb_sup_mult                         2
% 1.76/0.98  --comb_inst_mult                        10
% 1.76/0.98  
% 1.76/0.98  ------ Debug Options
% 1.76/0.98  
% 1.76/0.98  --dbg_backtrace                         false
% 1.76/0.98  --dbg_dump_prop_clauses                 false
% 1.76/0.98  --dbg_dump_prop_clauses_file            -
% 1.76/0.98  --dbg_out_stat                          false
% 1.76/0.98  ------ Parsing...
% 1.76/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.76/0.98  
% 1.76/0.98  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.76/0.98  
% 1.76/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.76/0.98  
% 1.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.76/0.98  ------ Proving...
% 1.76/0.98  ------ Problem Properties 
% 1.76/0.98  
% 1.76/0.98  
% 1.76/0.98  clauses                                 15
% 1.76/0.98  conjectures                             7
% 1.76/0.98  EPR                                     3
% 1.76/0.98  Horn                                    15
% 1.76/0.98  unary                                   12
% 1.76/0.98  binary                                  0
% 1.76/0.98  lits                                    21
% 1.76/0.98  lits eq                                 11
% 1.76/0.98  fd_pure                                 0
% 1.76/0.98  fd_pseudo                               0
% 1.76/0.98  fd_cond                                 0
% 1.76/0.98  fd_pseudo_cond                          2
% 1.76/0.98  AC symbols                              0
% 1.76/0.98  
% 1.76/0.98  ------ Schedule dynamic 5 is on 
% 1.76/0.98  
% 1.76/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.76/0.98  
% 1.76/0.98  
% 1.76/0.98  ------ 
% 1.76/0.98  Current options:
% 1.76/0.98  ------ 
% 1.76/0.98  
% 1.76/0.98  ------ Input Options
% 1.76/0.98  
% 1.76/0.98  --out_options                           all
% 1.76/0.98  --tptp_safe_out                         true
% 1.76/0.98  --problem_path                          ""
% 1.76/0.98  --include_path                          ""
% 1.76/0.98  --clausifier                            res/vclausify_rel
% 1.76/0.98  --clausifier_options                    --mode clausify
% 1.76/0.98  --stdin                                 false
% 1.76/0.98  --stats_out                             all
% 1.76/0.98  
% 1.76/0.98  ------ General Options
% 1.76/0.98  
% 1.76/0.98  --fof                                   false
% 1.76/0.98  --time_out_real                         305.
% 1.76/0.98  --time_out_virtual                      -1.
% 1.76/0.98  --symbol_type_check                     false
% 1.76/0.98  --clausify_out                          false
% 1.76/0.98  --sig_cnt_out                           false
% 1.76/0.98  --trig_cnt_out                          false
% 1.76/0.98  --trig_cnt_out_tolerance                1.
% 1.76/0.98  --trig_cnt_out_sk_spl                   false
% 1.76/0.98  --abstr_cl_out                          false
% 1.76/0.98  
% 1.76/0.98  ------ Global Options
% 1.76/0.98  
% 1.76/0.98  --schedule                              default
% 1.76/0.98  --add_important_lit                     false
% 1.76/0.98  --prop_solver_per_cl                    1000
% 1.76/0.98  --min_unsat_core                        false
% 1.76/0.98  --soft_assumptions                      false
% 1.76/0.98  --soft_lemma_size                       3
% 1.76/0.98  --prop_impl_unit_size                   0
% 1.76/0.98  --prop_impl_unit                        []
% 1.76/0.98  --share_sel_clauses                     true
% 1.76/0.98  --reset_solvers                         false
% 1.76/0.98  --bc_imp_inh                            [conj_cone]
% 1.76/0.98  --conj_cone_tolerance                   3.
% 1.76/0.98  --extra_neg_conj                        none
% 1.76/0.98  --large_theory_mode                     true
% 1.76/0.98  --prolific_symb_bound                   200
% 1.76/0.98  --lt_threshold                          2000
% 1.76/0.98  --clause_weak_htbl                      true
% 1.76/0.98  --gc_record_bc_elim                     false
% 1.76/0.98  
% 1.76/0.98  ------ Preprocessing Options
% 1.76/0.98  
% 1.76/0.98  --preprocessing_flag                    true
% 1.76/0.98  --time_out_prep_mult                    0.1
% 1.76/0.98  --splitting_mode                        input
% 1.76/0.98  --splitting_grd                         true
% 1.76/0.98  --splitting_cvd                         false
% 1.76/0.98  --splitting_cvd_svl                     false
% 1.76/0.98  --splitting_nvd                         32
% 1.76/0.98  --sub_typing                            true
% 1.76/0.98  --prep_gs_sim                           true
% 1.76/0.98  --prep_unflatten                        true
% 1.76/0.98  --prep_res_sim                          true
% 1.76/0.98  --prep_upred                            true
% 1.76/0.98  --prep_sem_filter                       exhaustive
% 1.76/0.98  --prep_sem_filter_out                   false
% 1.76/0.98  --pred_elim                             true
% 1.76/0.98  --res_sim_input                         true
% 1.76/0.98  --eq_ax_congr_red                       true
% 1.76/0.98  --pure_diseq_elim                       true
% 1.76/0.98  --brand_transform                       false
% 1.76/0.98  --non_eq_to_eq                          false
% 1.76/0.98  --prep_def_merge                        true
% 1.76/0.98  --prep_def_merge_prop_impl              false
% 1.76/0.98  --prep_def_merge_mbd                    true
% 1.76/0.98  --prep_def_merge_tr_red                 false
% 1.76/0.98  --prep_def_merge_tr_cl                  false
% 1.76/0.98  --smt_preprocessing                     true
% 1.76/0.98  --smt_ac_axioms                         fast
% 1.76/0.98  --preprocessed_out                      false
% 1.76/0.98  --preprocessed_stats                    false
% 1.76/0.98  
% 1.76/0.98  ------ Abstraction refinement Options
% 1.76/0.98  
% 1.76/0.98  --abstr_ref                             []
% 1.76/0.98  --abstr_ref_prep                        false
% 1.76/0.98  --abstr_ref_until_sat                   false
% 1.76/0.98  --abstr_ref_sig_restrict                funpre
% 1.76/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/0.98  --abstr_ref_under                       []
% 1.76/0.98  
% 1.76/0.98  ------ SAT Options
% 1.76/0.98  
% 1.76/0.98  --sat_mode                              false
% 1.76/0.98  --sat_fm_restart_options                ""
% 1.76/0.98  --sat_gr_def                            false
% 1.76/0.98  --sat_epr_types                         true
% 1.76/0.98  --sat_non_cyclic_types                  false
% 1.76/0.98  --sat_finite_models                     false
% 1.76/0.98  --sat_fm_lemmas                         false
% 1.76/0.98  --sat_fm_prep                           false
% 1.76/0.98  --sat_fm_uc_incr                        true
% 1.76/0.98  --sat_out_model                         small
% 1.76/0.98  --sat_out_clauses                       false
% 1.76/0.98  
% 1.76/0.98  ------ QBF Options
% 1.76/0.98  
% 1.76/0.98  --qbf_mode                              false
% 1.76/0.98  --qbf_elim_univ                         false
% 1.76/0.98  --qbf_dom_inst                          none
% 1.76/0.98  --qbf_dom_pre_inst                      false
% 1.76/0.98  --qbf_sk_in                             false
% 1.76/0.98  --qbf_pred_elim                         true
% 1.76/0.98  --qbf_split                             512
% 1.76/0.98  
% 1.76/0.98  ------ BMC1 Options
% 1.76/0.98  
% 1.76/0.98  --bmc1_incremental                      false
% 1.76/0.98  --bmc1_axioms                           reachable_all
% 1.76/0.98  --bmc1_min_bound                        0
% 1.76/0.98  --bmc1_max_bound                        -1
% 1.76/0.98  --bmc1_max_bound_default                -1
% 1.76/0.98  --bmc1_symbol_reachability              true
% 1.76/0.98  --bmc1_property_lemmas                  false
% 1.76/0.98  --bmc1_k_induction                      false
% 1.76/0.98  --bmc1_non_equiv_states                 false
% 1.76/0.98  --bmc1_deadlock                         false
% 1.76/0.98  --bmc1_ucm                              false
% 1.76/0.98  --bmc1_add_unsat_core                   none
% 1.76/0.98  --bmc1_unsat_core_children              false
% 1.76/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/0.98  --bmc1_out_stat                         full
% 1.76/0.98  --bmc1_ground_init                      false
% 1.76/0.98  --bmc1_pre_inst_next_state              false
% 1.76/0.98  --bmc1_pre_inst_state                   false
% 1.76/0.98  --bmc1_pre_inst_reach_state             false
% 1.76/0.98  --bmc1_out_unsat_core                   false
% 1.76/0.98  --bmc1_aig_witness_out                  false
% 1.76/0.98  --bmc1_verbose                          false
% 1.76/0.98  --bmc1_dump_clauses_tptp                false
% 1.76/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.76/0.98  --bmc1_dump_file                        -
% 1.76/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.76/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.76/0.98  --bmc1_ucm_extend_mode                  1
% 1.76/0.98  --bmc1_ucm_init_mode                    2
% 1.76/0.98  --bmc1_ucm_cone_mode                    none
% 1.76/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.76/0.98  --bmc1_ucm_relax_model                  4
% 1.76/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.76/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/0.98  --bmc1_ucm_layered_model                none
% 1.76/0.98  --bmc1_ucm_max_lemma_size               10
% 1.76/0.98  
% 1.76/0.98  ------ AIG Options
% 1.76/0.98  
% 1.76/0.98  --aig_mode                              false
% 1.76/0.98  
% 1.76/0.98  ------ Instantiation Options
% 1.76/0.98  
% 1.76/0.98  --instantiation_flag                    true
% 1.76/0.98  --inst_sos_flag                         false
% 1.76/0.98  --inst_sos_phase                        true
% 1.76/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/0.98  --inst_lit_sel_side                     none
% 1.76/0.98  --inst_solver_per_active                1400
% 1.76/0.98  --inst_solver_calls_frac                1.
% 1.76/0.98  --inst_passive_queue_type               priority_queues
% 1.76/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/0.98  --inst_passive_queues_freq              [25;2]
% 1.76/0.98  --inst_dismatching                      true
% 1.76/0.98  --inst_eager_unprocessed_to_passive     true
% 1.76/0.98  --inst_prop_sim_given                   true
% 1.76/0.98  --inst_prop_sim_new                     false
% 1.76/0.98  --inst_subs_new                         false
% 1.76/0.98  --inst_eq_res_simp                      false
% 1.76/0.98  --inst_subs_given                       false
% 1.76/0.98  --inst_orphan_elimination               true
% 1.76/0.98  --inst_learning_loop_flag               true
% 1.76/0.98  --inst_learning_start                   3000
% 1.76/0.98  --inst_learning_factor                  2
% 1.76/0.98  --inst_start_prop_sim_after_learn       3
% 1.76/0.98  --inst_sel_renew                        solver
% 1.76/0.98  --inst_lit_activity_flag                true
% 1.76/0.98  --inst_restr_to_given                   false
% 1.76/0.98  --inst_activity_threshold               500
% 1.76/0.98  --inst_out_proof                        true
% 1.76/0.98  
% 1.76/0.98  ------ Resolution Options
% 1.76/0.98  
% 1.76/0.98  --resolution_flag                       false
% 1.76/0.98  --res_lit_sel                           adaptive
% 1.76/0.98  --res_lit_sel_side                      none
% 1.76/0.99  --res_ordering                          kbo
% 1.76/0.99  --res_to_prop_solver                    active
% 1.76/0.99  --res_prop_simpl_new                    false
% 1.76/0.99  --res_prop_simpl_given                  true
% 1.76/0.99  --res_passive_queue_type                priority_queues
% 1.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/0.99  --res_passive_queues_freq               [15;5]
% 1.76/0.99  --res_forward_subs                      full
% 1.76/0.99  --res_backward_subs                     full
% 1.76/0.99  --res_forward_subs_resolution           true
% 1.76/0.99  --res_backward_subs_resolution          true
% 1.76/0.99  --res_orphan_elimination                true
% 1.76/0.99  --res_time_limit                        2.
% 1.76/0.99  --res_out_proof                         true
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Options
% 1.76/0.99  
% 1.76/0.99  --superposition_flag                    true
% 1.76/0.99  --sup_passive_queue_type                priority_queues
% 1.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.76/0.99  --demod_completeness_check              fast
% 1.76/0.99  --demod_use_ground                      true
% 1.76/0.99  --sup_to_prop_solver                    passive
% 1.76/0.99  --sup_prop_simpl_new                    true
% 1.76/0.99  --sup_prop_simpl_given                  true
% 1.76/0.99  --sup_fun_splitting                     false
% 1.76/0.99  --sup_smt_interval                      50000
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Simplification Setup
% 1.76/0.99  
% 1.76/0.99  --sup_indices_passive                   []
% 1.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_full_bw                           [BwDemod]
% 1.76/0.99  --sup_immed_triv                        [TrivRules]
% 1.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_immed_bw_main                     []
% 1.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  
% 1.76/0.99  ------ Combination Options
% 1.76/0.99  
% 1.76/0.99  --comb_res_mult                         3
% 1.76/0.99  --comb_sup_mult                         2
% 1.76/0.99  --comb_inst_mult                        10
% 1.76/0.99  
% 1.76/0.99  ------ Debug Options
% 1.76/0.99  
% 1.76/0.99  --dbg_backtrace                         false
% 1.76/0.99  --dbg_dump_prop_clauses                 false
% 1.76/0.99  --dbg_dump_prop_clauses_file            -
% 1.76/0.99  --dbg_out_stat                          false
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  ------ Proving...
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  % SZS output start Saturation for theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  fof(f7,axiom,(
% 1.76/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (r2_yellow_0(X0,X2) => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f20,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : ((! [X2] : (k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) | ~r2_yellow_0(X0,X2)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.76/0.99    inference(ennf_transformation,[],[f7])).
% 1.76/0.99  
% 1.76/0.99  fof(f21,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) | ~r2_yellow_0(X0,X2)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.76/0.99    inference(flattening,[],[f20])).
% 1.76/0.99  
% 1.76/0.99  fof(f44,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) | ~r2_yellow_0(X0,X2) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f21])).
% 1.76/0.99  
% 1.76/0.99  fof(f6,axiom,(
% 1.76/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (r1_yellow_0(X0,X2) => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f18,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : ((! [X2] : (k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) | ~r1_yellow_0(X0,X2)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.76/0.99    inference(ennf_transformation,[],[f6])).
% 1.76/0.99  
% 1.76/0.99  fof(f19,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : (k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) | ~r1_yellow_0(X0,X2)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.76/0.99    inference(flattening,[],[f18])).
% 1.76/0.99  
% 1.76/0.99  fof(f43,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) | ~r1_yellow_0(X0,X2) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f19])).
% 1.76/0.99  
% 1.76/0.99  fof(f5,axiom,(
% 1.76/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : ((r2_yellow_0(X0,X2) => r2_yellow_0(X1,X2)) & (r1_yellow_0(X0,X2) => r1_yellow_0(X1,X2))))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f16,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : ((! [X2] : ((r2_yellow_0(X1,X2) | ~r2_yellow_0(X0,X2)) & (r1_yellow_0(X1,X2) | ~r1_yellow_0(X0,X2))) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.76/0.99    inference(ennf_transformation,[],[f5])).
% 1.76/0.99  
% 1.76/0.99  fof(f17,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_yellow_0(X1,X2) | ~r2_yellow_0(X0,X2)) & (r1_yellow_0(X1,X2) | ~r1_yellow_0(X0,X2))) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 1.76/0.99    inference(flattening,[],[f16])).
% 1.76/0.99  
% 1.76/0.99  fof(f41,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (r1_yellow_0(X1,X2) | ~r1_yellow_0(X0,X2) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f17])).
% 1.76/0.99  
% 1.76/0.99  fof(f42,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (r2_yellow_0(X1,X2) | ~r2_yellow_0(X0,X2) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f17])).
% 1.76/0.99  
% 1.76/0.99  fof(f9,conjecture,(
% 1.76/0.99    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) => (X6 = X7 => ((r3_waybel_0(X0,X1,X4,X6) => r3_waybel_0(X2,X3,X5,X7)) & (r4_waybel_0(X0,X1,X4,X6) => r4_waybel_0(X2,X3,X5,X7))))))))))))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f10,negated_conjecture,(
% 1.76/0.99    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2))) => (X6 = X7 => ((r3_waybel_0(X0,X1,X4,X6) => r3_waybel_0(X2,X3,X5,X7)) & (r4_waybel_0(X0,X1,X4,X6) => r4_waybel_0(X2,X3,X5,X7))))))))))))))),
% 1.76/0.99    inference(negated_conjecture,[],[f9])).
% 1.76/0.99  
% 1.76/0.99  fof(f24,plain,(
% 1.76/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((? [X6] : (? [X7] : ((((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & (l1_orders_2(X3) & ~v2_struct_0(X3))) & (l1_orders_2(X2) & ~v2_struct_0(X2))) & (l1_orders_2(X1) & ~v2_struct_0(X1))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f10])).
% 1.76/0.99  
% 1.76/0.99  fof(f25,plain,(
% 1.76/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & l1_orders_2(X3) & ~v2_struct_0(X3)) & l1_orders_2(X2) & ~v2_struct_0(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f24])).
% 1.76/0.99  
% 1.76/0.99  fof(f34,plain,(
% 1.76/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) => (((~r3_waybel_0(X2,X3,X5,sK7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,sK7) & r4_waybel_0(X0,X1,X4,X6))) & sK7 = X6 & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f33,plain,(
% 1.76/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,sK6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,sK6))) & sK6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f32,plain,(
% 1.76/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,sK5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,sK5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(sK5))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f31,plain,(
% 1.76/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,sK4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,sK4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),sK4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f30,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & l1_orders_2(X3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,sK3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,sK3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(sK3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & l1_orders_2(sK3) & ~v2_struct_0(sK3))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f29,plain,(
% 1.76/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & l1_orders_2(X3) & ~v2_struct_0(X3)) & l1_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(sK2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(sK2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) & l1_orders_2(X3) & ~v2_struct_0(X3)) & l1_orders_2(sK2) & ~v2_struct_0(sK2))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f28,plain,(
% 1.76/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & l1_orders_2(X3) & ~v2_struct_0(X3)) & l1_orders_2(X2) & ~v2_struct_0(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,sK1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,sK1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & l1_orders_2(X3) & ~v2_struct_0(X3)) & l1_orders_2(X2) & ~v2_struct_0(X2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1))) )),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f27,plain,(
% 1.76/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(X0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(X0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & l1_orders_2(X3) & ~v2_struct_0(X3)) & l1_orders_2(X2) & ~v2_struct_0(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r3_waybel_0(X2,X3,X5,X7) & r3_waybel_0(sK0,X1,X4,X6)) | (~r4_waybel_0(X2,X3,X5,X7) & r4_waybel_0(sK0,X1,X4,X6))) & X6 = X7 & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X2)))) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X3),X4,X5) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & l1_orders_2(X3) & ~v2_struct_0(X3)) & l1_orders_2(X2) & ~v2_struct_0(X2)) & l1_orders_2(X1) & ~v2_struct_0(X1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f35,plain,(
% 1.76/0.99    (((((((((~r3_waybel_0(sK2,sK3,sK5,sK7) & r3_waybel_0(sK0,sK1,sK4,sK6)) | (~r4_waybel_0(sK2,sK3,sK5,sK7) & r4_waybel_0(sK0,sK1,sK4,sK6))) & sK6 = sK7 & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & l1_orders_2(sK3) & ~v2_struct_0(sK3)) & l1_orders_2(sK2) & ~v2_struct_0(sK2)) & l1_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f25,f34,f33,f32,f31,f30,f29,f28,f27])).
% 1.76/0.99  
% 1.76/0.99  fof(f56,plain,(
% 1.76/0.99    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f4,axiom,(
% 1.76/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f15,plain,(
% 1.76/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.76/0.99    inference(ennf_transformation,[],[f4])).
% 1.76/0.99  
% 1.76/0.99  fof(f40,plain,(
% 1.76/0.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.76/0.99    inference(cnf_transformation,[],[f15])).
% 1.76/0.99  
% 1.76/0.99  fof(f3,axiom,(
% 1.76/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f14,plain,(
% 1.76/0.99    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.76/0.99    inference(ennf_transformation,[],[f3])).
% 1.76/0.99  
% 1.76/0.99  fof(f38,plain,(
% 1.76/0.99    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f14])).
% 1.76/0.99  
% 1.76/0.99  fof(f50,plain,(
% 1.76/0.99    l1_orders_2(sK1)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f55,plain,(
% 1.76/0.99    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f48,plain,(
% 1.76/0.99    l1_orders_2(sK0)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f39,plain,(
% 1.76/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.76/0.99    inference(cnf_transformation,[],[f15])).
% 1.76/0.99  
% 1.76/0.99  fof(f70,plain,(
% 1.76/0.99    ~r3_waybel_0(sK2,sK3,sK5,sK7) | ~r4_waybel_0(sK2,sK3,sK5,sK7)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f68,plain,(
% 1.76/0.99    r3_waybel_0(sK0,sK1,sK4,sK6) | ~r4_waybel_0(sK2,sK3,sK5,sK7)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f66,plain,(
% 1.76/0.99    sK6 = sK7),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f69,plain,(
% 1.76/0.99    ~r3_waybel_0(sK2,sK3,sK5,sK7) | r4_waybel_0(sK0,sK1,sK4,sK6)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f67,plain,(
% 1.76/0.99    r3_waybel_0(sK0,sK1,sK4,sK6) | r4_waybel_0(sK0,sK1,sK4,sK6)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f8,axiom,(
% 1.76/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f22,plain,(
% 1.76/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.76/0.99    inference(ennf_transformation,[],[f8])).
% 1.76/0.99  
% 1.76/0.99  fof(f23,plain,(
% 1.76/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.76/0.99    inference(flattening,[],[f22])).
% 1.76/0.99  
% 1.76/0.99  fof(f26,plain,(
% 1.76/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.76/0.99    inference(nnf_transformation,[],[f23])).
% 1.76/0.99  
% 1.76/0.99  fof(f45,plain,(
% 1.76/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f26])).
% 1.76/0.99  
% 1.76/0.99  fof(f63,plain,(
% 1.76/0.99    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f54,plain,(
% 1.76/0.99    l1_orders_2(sK3)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f57,plain,(
% 1.76/0.99    v1_funct_1(sK4)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f58,plain,(
% 1.76/0.99    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f59,plain,(
% 1.76/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f60,plain,(
% 1.76/0.99    v1_funct_1(sK5)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f61,plain,(
% 1.76/0.99    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f62,plain,(
% 1.76/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f2,axiom,(
% 1.76/0.99    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f13,plain,(
% 1.76/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.76/0.99    inference(ennf_transformation,[],[f2])).
% 1.76/0.99  
% 1.76/0.99  fof(f37,plain,(
% 1.76/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f13])).
% 1.76/0.99  
% 1.76/0.99  fof(f1,axiom,(
% 1.76/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f11,plain,(
% 1.76/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f1])).
% 1.76/0.99  
% 1.76/0.99  fof(f12,plain,(
% 1.76/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.76/0.99    inference(flattening,[],[f11])).
% 1.76/0.99  
% 1.76/0.99  fof(f36,plain,(
% 1.76/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f12])).
% 1.76/0.99  
% 1.76/0.99  fof(f53,plain,(
% 1.76/0.99    ~v2_struct_0(sK3)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f49,plain,(
% 1.76/0.99    ~v2_struct_0(sK1)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f52,plain,(
% 1.76/0.99    l1_orders_2(sK2)),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  fof(f65,plain,(
% 1.76/0.99    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.76/0.99    inference(cnf_transformation,[],[f35])).
% 1.76/0.99  
% 1.76/0.99  cnf(c_297,plain,
% 1.76/0.99      ( ~ r4_waybel_0(X0,X1,X2,X3)
% 1.76/0.99      | r4_waybel_0(X4,X5,X6,X7)
% 1.76/0.99      | X6 != X2
% 1.76/0.99      | X4 != X0
% 1.76/0.99      | X5 != X1
% 1.76/0.99      | X7 != X3 ),
% 1.76/0.99      theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_296,plain,
% 1.76/0.99      ( ~ r3_waybel_0(X0,X1,X2,X3)
% 1.76/0.99      | r3_waybel_0(X4,X5,X6,X7)
% 1.76/0.99      | X6 != X2
% 1.76/0.99      | X4 != X0
% 1.76/0.99      | X5 != X1
% 1.76/0.99      | X7 != X3 ),
% 1.76/0.99      theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_295,plain,
% 1.76/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 1.76/0.99      theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_294,plain,
% 1.76/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.76/0.99      | v1_funct_2(X3,X4,X5)
% 1.76/0.99      | X5 != X2
% 1.76/0.99      | X3 != X0
% 1.76/0.99      | X4 != X1 ),
% 1.76/0.99      theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_293,plain,
% 1.76/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 1.76/0.99      | r1_funct_2(X6,X7,X8,X9,X10,X11)
% 1.76/0.99      | X8 != X2
% 1.76/0.99      | X6 != X0
% 1.76/0.99      | X7 != X1
% 1.76/0.99      | X9 != X3
% 1.76/0.99      | X10 != X4
% 1.76/0.99      | X11 != X5 ),
% 1.76/0.99      theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_287,plain,
% 1.76/0.99      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.76/0.99      theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_286,plain,
% 1.76/0.99      ( ~ v2_struct_0(X0) | v2_struct_0(X1) | X1 != X0 ),
% 1.76/0.99      theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_285,plain,
% 1.76/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.76/0.99      theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1051,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_8,plain,
% 1.76/0.99      ( ~ r2_yellow_0(X0,X1)
% 1.76/0.99      | ~ l1_orders_2(X0)
% 1.76/0.99      | ~ l1_orders_2(X2)
% 1.76/0.99      | k2_yellow_0(X2,X1) = k2_yellow_0(X0,X1)
% 1.76/0.99      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_7,plain,
% 1.76/0.99      ( ~ r1_yellow_0(X0,X1)
% 1.76/0.99      | ~ l1_orders_2(X0)
% 1.76/0.99      | ~ l1_orders_2(X2)
% 1.76/0.99      | k1_yellow_0(X2,X1) = k1_yellow_0(X0,X1)
% 1.76/0.99      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_6,plain,
% 1.76/0.99      ( ~ r1_yellow_0(X0,X1)
% 1.76/0.99      | r1_yellow_0(X2,X1)
% 1.76/0.99      | ~ l1_orders_2(X0)
% 1.76/0.99      | ~ l1_orders_2(X2)
% 1.76/0.99      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_5,plain,
% 1.76/0.99      ( ~ r2_yellow_0(X0,X1)
% 1.76/0.99      | r2_yellow_0(X2,X1)
% 1.76/0.99      | ~ l1_orders_2(X0)
% 1.76/0.99      | ~ l1_orders_2(X2)
% 1.76/0.99      | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_25,negated_conjecture,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_3,plain,
% 1.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.76/0.99      | X2 = X0
% 1.76/0.99      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1230,plain,
% 1.76/0.99      ( X0 = X1
% 1.76/0.99      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 1.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1837,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_orders_2(sK1) = X1
% 1.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_25,c_1230]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.76/0.99      | ~ l1_orders_2(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_31,negated_conjecture,
% 1.76/0.99      ( l1_orders_2(sK1) ),
% 1.76/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_410,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.76/0.99      | sK1 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_31]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_411,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_412,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1839,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_orders_2(sK1) = X1
% 1.76/0.99      | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_25,c_1230]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1971,plain,
% 1.76/0.99      ( u1_orders_2(sK1) = X1
% 1.76/0.99      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1837,c_412,c_1839]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1972,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_orders_2(sK1) = X1 ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_1971]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1978,plain,
% 1.76/0.99      ( u1_orders_2(sK3) = u1_orders_2(sK1) ),
% 1.76/0.99      inference(equality_resolution,[status(thm)],[c_1972]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_26,negated_conjecture,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1838,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_orders_2(sK0) = X1
% 1.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_26,c_1230]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_33,negated_conjecture,
% 1.76/0.99      ( l1_orders_2(sK0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_36,plain,
% 1.76/0.99      ( l1_orders_2(sK0) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_74,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 1.76/0.99      | l1_orders_2(X0) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_76,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
% 1.76/0.99      | l1_orders_2(sK0) != iProver_top ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_74]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1840,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_orders_2(sK0) = X1
% 1.76/0.99      | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_26,c_1230]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2110,plain,
% 1.76/0.99      ( u1_orders_2(sK0) = X1
% 1.76/0.99      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1838,c_36,c_76,c_1840]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2111,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_orders_2(sK0) = X1 ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_2110]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2115,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
% 1.76/0.99      | u1_orders_2(sK0) = u1_orders_2(sK1) ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_25,c_2111]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2554,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
% 1.76/0.99      | u1_orders_2(sK0) = u1_orders_2(sK3) ),
% 1.76/0.99      inference(demodulation,[status(thm)],[c_1978,c_2115]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2117,plain,
% 1.76/0.99      ( u1_orders_2(sK2) = u1_orders_2(sK0) ),
% 1.76/0.99      inference(equality_resolution,[status(thm)],[c_2111]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2887,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
% 1.76/0.99      | u1_orders_2(sK2) = u1_orders_2(sK3) ),
% 1.76/0.99      inference(light_normalisation,[status(thm)],[c_2554,c_2117]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_4,plain,
% 1.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.76/0.99      | X2 = X1
% 1.76/0.99      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1229,plain,
% 1.76/0.99      ( X0 = X1
% 1.76/0.99      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 1.76/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1776,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK0) = X0
% 1.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_26,c_1229]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_75,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
% 1.76/0.99      | ~ l1_orders_2(sK0) ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1778,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK0) = X0
% 1.76/0.99      | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_26,c_1229]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1813,plain,
% 1.76/0.99      ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
% 1.76/0.99      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK0) = X0 ),
% 1.76/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1778]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1952,plain,
% 1.76/0.99      ( u1_struct_0(sK0) = X0
% 1.76/0.99      | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1776,c_33,c_75,c_1813]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1953,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK0) = X0 ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_1952]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1959,plain,
% 1.76/0.99      ( u1_struct_0(sK0) = u1_struct_0(sK2) ),
% 1.76/0.99      inference(equality_resolution,[status(thm)],[c_1953]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1957,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
% 1.76/0.99      | u1_struct_0(sK1) = u1_struct_0(sK0) ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_25,c_1953]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1775,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK1) = X0
% 1.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_25,c_1229]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1777,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK1) = X0
% 1.76/0.99      | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
% 1.76/0.99      inference(superposition,[status(thm)],[c_25,c_1229]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1810,plain,
% 1.76/0.99      ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
% 1.76/0.99      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK1) = X0 ),
% 1.76/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1777]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1879,plain,
% 1.76/0.99      ( u1_struct_0(sK1) = X0
% 1.76/0.99      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1775,c_411,c_1810]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1880,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK1) = X0 ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_1879]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1886,plain,
% 1.76/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK1) ),
% 1.76/0.99      inference(equality_resolution,[status(thm)],[c_1880]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2141,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
% 1.76/0.99      | u1_struct_0(sK3) = u1_struct_0(sK0) ),
% 1.76/0.99      inference(light_normalisation,[status(thm)],[c_1957,c_1886]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2516,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
% 1.76/0.99      | u1_struct_0(sK3) = u1_struct_0(sK2) ),
% 1.76/0.99      inference(demodulation,[status(thm)],[c_1959,c_2141]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2119,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_orders_2(sK2) = X1 ),
% 1.76/0.99      inference(demodulation,[status(thm)],[c_2117,c_2111]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1980,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_orders_2(sK3) = X1 ),
% 1.76/0.99      inference(demodulation,[status(thm)],[c_1978,c_1972]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1961,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK2) = X0 ),
% 1.76/0.99      inference(demodulation,[status(thm)],[c_1959,c_1953]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1888,plain,
% 1.76/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 1.76/0.99      | u1_struct_0(sK3) = X0 ),
% 1.76/0.99      inference(demodulation,[status(thm)],[c_1886,c_1880]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_11,negated_conjecture,
% 1.76/0.99      ( ~ r4_waybel_0(sK2,sK3,sK5,sK7) | ~ r3_waybel_0(sK2,sK3,sK5,sK7) ),
% 1.76/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_13,negated_conjecture,
% 1.76/0.99      ( ~ r4_waybel_0(sK2,sK3,sK5,sK7) | r3_waybel_0(sK0,sK1,sK4,sK6) ),
% 1.76/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_463,plain,
% 1.76/0.99      ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
% 1.76/0.99      | sK6 != sK7
% 1.76/0.99      | sK4 != sK5
% 1.76/0.99      | sK1 != sK3
% 1.76/0.99      | sK0 != sK2 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_13]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_15,negated_conjecture,
% 1.76/0.99      ( sK6 = sK7 ),
% 1.76/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_465,plain,
% 1.76/0.99      ( ~ r4_waybel_0(sK2,sK3,sK5,sK7) | sK4 != sK5 | sK1 != sK3 | sK0 != sK2 ),
% 1.76/0.99      inference(global_propositional_subsumption,[status(thm)],[c_463,c_15]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_12,negated_conjecture,
% 1.76/0.99      ( r4_waybel_0(sK0,sK1,sK4,sK6) | ~ r3_waybel_0(sK2,sK3,sK5,sK7) ),
% 1.76/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_14,negated_conjecture,
% 1.76/0.99      ( r4_waybel_0(sK0,sK1,sK4,sK6) | r3_waybel_0(sK0,sK1,sK4,sK6) ),
% 1.76/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_432,plain,
% 1.76/0.99      ( r4_waybel_0(sK0,sK1,sK4,sK6)
% 1.76/0.99      | sK6 != sK7
% 1.76/0.99      | sK4 != sK5
% 1.76/0.99      | sK1 != sK3
% 1.76/0.99      | sK0 != sK2 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_434,plain,
% 1.76/0.99      ( r4_waybel_0(sK0,sK1,sK4,sK6) | sK4 != sK5 | sK1 != sK3 | sK0 != sK2 ),
% 1.76/0.99      inference(global_propositional_subsumption,[status(thm)],[c_432,c_15]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_492,plain,
% 1.76/0.99      ( sK6 != sK7 | sK4 != sK5 | sK1 != sK3 | sK0 != sK2 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_465,c_434]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_493,plain,
% 1.76/0.99      ( sK4 != sK5 | sK1 != sK3 | sK0 != sK2 ),
% 1.76/0.99      inference(global_propositional_subsumption,[status(thm)],[c_492,c_15]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_10,plain,
% 1.76/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 1.76/0.99      | ~ v1_funct_2(X5,X2,X3)
% 1.76/0.99      | ~ v1_funct_2(X4,X0,X1)
% 1.76/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.76/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.76/0.99      | ~ v1_funct_1(X5)
% 1.76/0.99      | ~ v1_funct_1(X4)
% 1.76/0.99      | v1_xboole_0(X1)
% 1.76/0.99      | v1_xboole_0(X3)
% 1.76/0.99      | X4 = X5 ),
% 1.76/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_18,negated_conjecture,
% 1.76/0.99      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
% 1.76/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_509,plain,
% 1.76/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.76/0.99      | ~ v1_funct_2(X3,X4,X5)
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.76/0.99      | ~ v1_funct_1(X0)
% 1.76/0.99      | ~ v1_funct_1(X3)
% 1.76/0.99      | v1_xboole_0(X2)
% 1.76/0.99      | v1_xboole_0(X5)
% 1.76/0.99      | X3 = X0
% 1.76/0.99      | u1_struct_0(sK1) != X2
% 1.76/0.99      | u1_struct_0(sK0) != X1
% 1.76/0.99      | u1_struct_0(sK3) != X5
% 1.76/0.99      | u1_struct_0(sK2) != X4
% 1.76/0.99      | sK4 != X0
% 1.76/0.99      | sK5 != X3 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_510,plain,
% 1.76/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.76/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
% 1.76/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.76/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 1.76/0.99      | ~ v1_funct_1(sK4)
% 1.76/0.99      | ~ v1_funct_1(sK5)
% 1.76/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 1.76/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 1.76/0.99      | sK5 = sK4 ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_509]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_27,negated_conjecture,
% 1.76/0.99      ( l1_orders_2(sK3) ),
% 1.76/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_24,negated_conjecture,
% 1.76/0.99      ( v1_funct_1(sK4) ),
% 1.76/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_23,negated_conjecture,
% 1.76/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_22,negated_conjecture,
% 1.76/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.76/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_21,negated_conjecture,
% 1.76/0.99      ( v1_funct_1(sK5) ),
% 1.76/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_20,negated_conjecture,
% 1.76/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_19,negated_conjecture,
% 1.76/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 1.76/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1,plain,
% 1.76/0.99      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_0,plain,
% 1.76/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_326,plain,
% 1.76/0.99      ( ~ l1_orders_2(X0) | v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.76/0.99      inference(resolution,[status(thm)],[c_1,c_0]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_28,negated_conjecture,
% 1.76/0.99      ( ~ v2_struct_0(sK3) ),
% 1.76/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_344,plain,
% 1.76/0.99      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_326,c_28]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_345,plain,
% 1.76/0.99      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_344]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_32,negated_conjecture,
% 1.76/0.99      ( ~ v2_struct_0(sK1) ),
% 1.76/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_366,plain,
% 1.76/0.99      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_326,c_32]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_367,plain,
% 1.76/0.99      ( ~ l1_orders_2(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_366]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_512,plain,
% 1.76/0.99      ( sK5 = sK4 ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_510,c_31,c_27,c_24,c_23,c_22,c_21,c_20,c_19,c_345,c_367]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1257,plain,
% 1.76/0.99      ( sK1 != sK3 | sK0 != sK2 | sK5 != sK5 ),
% 1.76/0.99      inference(light_normalisation,[status(thm)],[c_493,c_512]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1258,plain,
% 1.76/0.99      ( sK1 != sK3 | sK0 != sK2 ),
% 1.76/0.99      inference(equality_resolution_simp,[status(thm)],[c_1257]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_29,negated_conjecture,
% 1.76/0.99      ( l1_orders_2(sK2) ),
% 1.76/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_403,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.76/0.99      | sK2 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_29]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_404,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_403]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1223,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_396,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.76/0.99      | sK3 != X0 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_397,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1224,plain,
% 1.76/0.99      ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_16,negated_conjecture,
% 1.76/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.76/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1228,plain,
% 1.76/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1226,plain,
% 1.76/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  % SZS output end Saturation for theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  ------                               Statistics
% 1.76/0.99  
% 1.76/0.99  ------ General
% 1.76/0.99  
% 1.76/0.99  abstr_ref_over_cycles:                  0
% 1.76/0.99  abstr_ref_under_cycles:                 0
% 1.76/0.99  gc_basic_clause_elim:                   0
% 1.76/0.99  forced_gc_time:                         0
% 1.76/0.99  parsing_time:                           0.009
% 1.76/0.99  unif_index_cands_time:                  0.
% 1.76/0.99  unif_index_add_time:                    0.
% 1.76/0.99  orderings_time:                         0.
% 1.76/0.99  out_proof_time:                         0.
% 1.76/0.99  total_time:                             0.126
% 1.76/0.99  num_of_symbols:                         58
% 1.76/0.99  num_of_terms:                           3857
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing
% 1.76/0.99  
% 1.76/0.99  num_of_splits:                          0
% 1.76/0.99  num_of_split_atoms:                     0
% 1.76/0.99  num_of_reused_defs:                     0
% 1.76/0.99  num_eq_ax_congr_red:                    9
% 1.76/0.99  num_of_sem_filtered_clauses:            5
% 1.76/0.99  num_of_subtypes:                        0
% 1.76/0.99  monotx_restored_types:                  0
% 1.76/0.99  sat_num_of_epr_types:                   0
% 1.76/0.99  sat_num_of_non_cyclic_types:            0
% 1.76/0.99  sat_guarded_non_collapsed_types:        0
% 1.76/0.99  num_pure_diseq_elim:                    0
% 1.76/0.99  simp_replaced_by:                       0
% 1.76/0.99  res_preprocessed:                       97
% 1.76/0.99  prep_upred:                             0
% 1.76/0.99  prep_unflattend:                        52
% 1.76/0.99  smt_new_axioms:                         0
% 1.76/0.99  pred_elim_cands:                        1
% 1.76/0.99  pred_elim:                              9
% 1.76/0.99  pred_elim_cl:                           16
% 1.76/0.99  pred_elim_cycles:                       11
% 1.76/0.99  merged_defs:                            0
% 1.76/0.99  merged_defs_ncl:                        0
% 1.76/0.99  bin_hyper_res:                          0
% 1.76/0.99  prep_cycles:                            4
% 1.76/0.99  pred_elim_time:                         0.01
% 1.76/0.99  splitting_time:                         0.
% 1.76/0.99  sem_filter_time:                        0.
% 1.76/0.99  monotx_time:                            0.
% 1.76/0.99  subtype_inf_time:                       0.
% 1.76/0.99  
% 1.76/0.99  ------ Problem properties
% 1.76/0.99  
% 1.76/0.99  clauses:                                15
% 1.76/0.99  conjectures:                            7
% 1.76/0.99  epr:                                    3
% 1.76/0.99  horn:                                   15
% 1.76/0.99  ground:                                 13
% 1.76/0.99  unary:                                  12
% 1.76/0.99  binary:                                 0
% 1.76/0.99  lits:                                   21
% 1.76/0.99  lits_eq:                                11
% 1.76/0.99  fd_pure:                                0
% 1.76/0.99  fd_pseudo:                              0
% 1.76/0.99  fd_cond:                                0
% 1.76/0.99  fd_pseudo_cond:                         2
% 1.76/0.99  ac_symbols:                             0
% 1.76/0.99  
% 1.76/0.99  ------ Propositional Solver
% 1.76/0.99  
% 1.76/0.99  prop_solver_calls:                      25
% 1.76/0.99  prop_fast_solver_calls:                 613
% 1.76/0.99  smt_solver_calls:                       0
% 1.76/0.99  smt_fast_solver_calls:                  0
% 1.76/0.99  prop_num_of_clauses:                    1310
% 1.76/0.99  prop_preprocess_simplified:             3572
% 1.76/0.99  prop_fo_subsumed:                       25
% 1.76/0.99  prop_solver_time:                       0.
% 1.76/0.99  smt_solver_time:                        0.
% 1.76/0.99  smt_fast_solver_time:                   0.
% 1.76/0.99  prop_fast_solver_time:                  0.
% 1.76/0.99  prop_unsat_core_time:                   0.
% 1.76/0.99  
% 1.76/0.99  ------ QBF
% 1.76/0.99  
% 1.76/0.99  qbf_q_res:                              0
% 1.76/0.99  qbf_num_tautologies:                    0
% 1.76/0.99  qbf_prep_cycles:                        0
% 1.76/0.99  
% 1.76/0.99  ------ BMC1
% 1.76/0.99  
% 1.76/0.99  bmc1_current_bound:                     -1
% 1.76/0.99  bmc1_last_solved_bound:                 -1
% 1.76/0.99  bmc1_unsat_core_size:                   -1
% 1.76/0.99  bmc1_unsat_core_parents_size:           -1
% 1.76/0.99  bmc1_merge_next_fun:                    0
% 1.76/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.76/0.99  
% 1.76/0.99  ------ Instantiation
% 1.76/0.99  
% 1.76/0.99  inst_num_of_clauses:                    411
% 1.76/0.99  inst_num_in_passive:                    32
% 1.76/0.99  inst_num_in_active:                     177
% 1.76/0.99  inst_num_in_unprocessed:                202
% 1.76/0.99  inst_num_of_loops:                      180
% 1.76/0.99  inst_num_of_learning_restarts:          0
% 1.76/0.99  inst_num_moves_active_passive:          1
% 1.76/0.99  inst_lit_activity:                      0
% 1.76/0.99  inst_lit_activity_moves:                0
% 1.76/0.99  inst_num_tautologies:                   0
% 1.76/0.99  inst_num_prop_implied:                  0
% 1.76/0.99  inst_num_existing_simplified:           0
% 1.76/0.99  inst_num_eq_res_simplified:             0
% 1.76/0.99  inst_num_child_elim:                    0
% 1.76/0.99  inst_num_of_dismatching_blockings:      74
% 1.76/0.99  inst_num_of_non_proper_insts:           314
% 1.76/0.99  inst_num_of_duplicates:                 0
% 1.76/0.99  inst_inst_num_from_inst_to_res:         0
% 1.76/0.99  inst_dismatching_checking_time:         0.
% 1.76/0.99  
% 1.76/0.99  ------ Resolution
% 1.76/0.99  
% 1.76/0.99  res_num_of_clauses:                     0
% 1.76/0.99  res_num_in_passive:                     0
% 1.76/0.99  res_num_in_active:                      0
% 1.76/0.99  res_num_of_loops:                       101
% 1.76/0.99  res_forward_subset_subsumed:            47
% 1.76/0.99  res_backward_subset_subsumed:           2
% 1.76/0.99  res_forward_subsumed:                   2
% 1.76/0.99  res_backward_subsumed:                  0
% 1.76/0.99  res_forward_subsumption_resolution:     0
% 1.76/0.99  res_backward_subsumption_resolution:    0
% 1.76/0.99  res_clause_to_clause_subsumption:       96
% 1.76/0.99  res_orphan_elimination:                 0
% 1.76/0.99  res_tautology_del:                      52
% 1.76/0.99  res_num_eq_res_simplified:              0
% 1.76/0.99  res_num_sel_changes:                    0
% 1.76/0.99  res_moves_from_active_to_pass:          0
% 1.76/0.99  
% 1.76/0.99  ------ Superposition
% 1.76/0.99  
% 1.76/0.99  sup_time_total:                         0.
% 1.76/0.99  sup_time_generating:                    0.
% 1.76/0.99  sup_time_sim_full:                      0.
% 1.76/0.99  sup_time_sim_immed:                     0.
% 1.76/0.99  
% 1.76/0.99  sup_num_of_clauses:                     25
% 1.76/0.99  sup_num_in_active:                      19
% 1.76/0.99  sup_num_in_passive:                     6
% 1.76/0.99  sup_num_of_loops:                       34
% 1.76/0.99  sup_fw_superposition:                   16
% 1.76/0.99  sup_bw_superposition:                   8
% 1.76/0.99  sup_immediate_simplified:               5
% 1.76/0.99  sup_given_eliminated:                   4
% 1.76/0.99  comparisons_done:                       0
% 1.76/0.99  comparisons_avoided:                    0
% 1.76/0.99  
% 1.76/0.99  ------ Simplifications
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  sim_fw_subset_subsumed:                 4
% 1.76/0.99  sim_bw_subset_subsumed:                 4
% 1.76/0.99  sim_fw_subsumed:                        0
% 1.76/0.99  sim_bw_subsumed:                        0
% 1.76/0.99  sim_fw_subsumption_res:                 0
% 1.76/0.99  sim_bw_subsumption_res:                 0
% 1.76/0.99  sim_tautology_del:                      0
% 1.76/0.99  sim_eq_tautology_del:                   12
% 1.76/0.99  sim_eq_res_simp:                        1
% 1.76/0.99  sim_fw_demodulated:                     0
% 1.76/0.99  sim_bw_demodulated:                     15
% 1.76/0.99  sim_light_normalised:                   7
% 1.76/0.99  sim_joinable_taut:                      0
% 1.76/0.99  sim_joinable_simp:                      0
% 1.76/0.99  sim_ac_normalised:                      0
% 1.76/0.99  sim_smt_subsumption:                    0
% 1.76/0.99  
%------------------------------------------------------------------------------
