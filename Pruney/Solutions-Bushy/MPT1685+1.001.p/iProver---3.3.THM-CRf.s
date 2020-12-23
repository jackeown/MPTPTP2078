%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1685+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:10 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  553 (423531 expanded)
%              Number of clauses        :  453 (67934 expanded)
%              Number of leaves         :   23 (216113 expanded)
%              Depth                    :   42
%              Number of atoms          : 2675 (8803696 expanded)
%              Number of equality atoms : 1128 (1208038 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r4_waybel_0(X0,X1,X2,X3)
                  <=> ( r1_yellow_0(X0,X3)
                     => ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r4_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_yellow_0(X0,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r4_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_yellow_0(X0,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r4_waybel_0(X0,X1,X2,X3)
                      | ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) != k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                          | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r1_yellow_0(X0,X3) ) )
                    & ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_yellow_0(X0,X3)
                      | ~ r4_waybel_0(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r4_waybel_0(X0,X1,X2,X3)
                      | ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) != k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                          | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r1_yellow_0(X0,X3) ) )
                    & ( ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                        & r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_yellow_0(X0,X3)
                      | ~ r4_waybel_0(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_waybel_0(X0,X1,X2,X3)
      | r1_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r3_waybel_0(X0,X1,X2,X3)
                  <=> ( r2_yellow_0(X0,X3)
                     => ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r3_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r2_yellow_0(X0,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r3_waybel_0(X0,X1,X2,X3)
                  <=> ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r2_yellow_0(X0,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r3_waybel_0(X0,X1,X2,X3)
                      | ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                          | ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r2_yellow_0(X0,X3) ) )
                    & ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r2_yellow_0(X0,X3)
                      | ~ r3_waybel_0(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r3_waybel_0(X0,X1,X2,X3)
                      | ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                          | ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                        & r2_yellow_0(X0,X3) ) )
                    & ( ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
                        & r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r2_yellow_0(X0,X3)
                      | ~ r3_waybel_0(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_waybel_0(X0,X1,X2,X3)
      | r2_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f40,f53,f52,f51,f50,f49,f48,f47,f46])).

fof(f101,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r2_yellow_0(X0,X2)
               => k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
              | ~ r2_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) = k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_yellow_0(X0,X3)
      | ~ r4_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK7)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f97,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_waybel_0(X0,X1,X2,X3)
      | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) != k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_yellow_0(X0,X3)
      | ~ r4_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
      | ~ r2_yellow_0(X0,X3)
      | ~ r3_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r2_yellow_0(X0,X3)
      | ~ r3_waybel_0(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_waybel_0(X0,X1,X2,X3)
      | k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3))
      | ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( r4_waybel_0(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_yellow_0(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1,plain,
    ( r3_waybel_0(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_yellow_0(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ r3_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2094,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_2095,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_2094])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_41,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2097,plain,
    ( r2_yellow_0(sK2,sK7)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2095,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_2098,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | r2_yellow_0(sK2,sK7) ),
    inference(renaming,[status(thm)],[c_2097])).

cnf(c_3145,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_2098])).

cnf(c_3146,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_yellow_0(sK2,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_3145])).

cnf(c_3148,plain,
    ( r2_yellow_0(sK2,sK7)
    | r1_yellow_0(sK2,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3146,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_3149,plain,
    ( r1_yellow_0(sK2,sK7)
    | r2_yellow_0(sK2,sK7) ),
    inference(renaming,[status(thm)],[c_3148])).

cnf(c_5537,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3149])).

cnf(c_38,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_20,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r1_yellow_0(X2,X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5552,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_yellow_0(X1,X2) != iProver_top
    | r1_yellow_0(X0,X2) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7138,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r1_yellow_0(X0,X1) != iProver_top
    | r1_yellow_0(sK0,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_5552])).

cnf(c_45,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_48,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_7256,plain,
    ( l1_orders_2(X0) != iProver_top
    | r1_yellow_0(sK0,X1) = iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7138,c_48])).

cnf(c_7257,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r1_yellow_0(X0,X1) != iProver_top
    | r1_yellow_0(sK0,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7256])).

cnf(c_7262,plain,
    ( r1_yellow_0(sK0,X0) = iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7257])).

cnf(c_52,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_8835,plain,
    ( r1_yellow_0(sK2,X0) != iProver_top
    | r1_yellow_0(sK0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7262,c_52])).

cnf(c_8836,plain,
    ( r1_yellow_0(sK0,X0) = iProver_top
    | r1_yellow_0(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8835])).

cnf(c_8841,plain,
    ( r1_yellow_0(sK0,sK7) = iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5537,c_8836])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_5556,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6659,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_5556])).

cnf(c_11,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_96,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6661,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_5556])).

cnf(c_6672,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6661])).

cnf(c_6923,plain,
    ( u1_orders_2(sK0) = X1
    | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6659,c_45,c_96,c_6672])).

cnf(c_6924,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1 ),
    inference(renaming,[status(thm)],[c_6923])).

cnf(c_6928,plain,
    ( u1_orders_2(sK2) = u1_orders_2(sK0) ),
    inference(equality_resolution,[status(thm)],[c_6924])).

cnf(c_21,plain,
    ( ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | k1_yellow_0(X2,X1) = k1_yellow_0(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5551,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
    | r1_yellow_0(X1,X2) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8103,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK0,X1)
    | r1_yellow_0(sK0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6928,c_5551])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_5555,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6641,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_5555])).

cnf(c_95,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_97,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_6643,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_5555])).

cnf(c_6725,plain,
    ( u1_struct_0(sK0) = X0
    | g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6641,c_48,c_97,c_6643])).

cnf(c_6726,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(renaming,[status(thm)],[c_6725])).

cnf(c_6730,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK2) ),
    inference(equality_resolution,[status(thm)],[c_6726])).

cnf(c_8105,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK0,X1)
    | r1_yellow_0(sK0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8103,c_6730])).

cnf(c_10555,plain,
    ( l1_orders_2(X0) != iProver_top
    | r1_yellow_0(sK0,X1) != iProver_top
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8105,c_48])).

cnf(c_10556,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK0,X1)
    | r1_yellow_0(sK0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10555])).

cnf(c_10563,plain,
    ( k1_yellow_0(sK0,X0) = k1_yellow_0(sK2,X0)
    | r1_yellow_0(sK0,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10556])).

cnf(c_12646,plain,
    ( r1_yellow_0(sK0,X0) != iProver_top
    | k1_yellow_0(sK0,X0) = k1_yellow_0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10563,c_52])).

cnf(c_12647,plain,
    ( k1_yellow_0(sK0,X0) = k1_yellow_0(sK2,X0)
    | r1_yellow_0(sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12646])).

cnf(c_12654,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7)
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_8841,c_12647])).

cnf(c_22,plain,
    ( ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
    | k2_yellow_0(X2,X1) = k2_yellow_0(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_5550,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
    | r2_yellow_0(X1,X2) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8078,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | r2_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6928,c_5550])).

cnf(c_8085,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | r2_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8078,c_6730])).

cnf(c_10540,plain,
    ( l1_orders_2(X0) != iProver_top
    | r2_yellow_0(X0,X1) != iProver_top
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8085,c_48])).

cnf(c_10541,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | r2_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10540])).

cnf(c_10548,plain,
    ( k2_yellow_0(sK0,X0) = k2_yellow_0(sK2,X0)
    | r2_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10541])).

cnf(c_12568,plain,
    ( r2_yellow_0(sK2,X0) != iProver_top
    | k2_yellow_0(sK0,X0) = k2_yellow_0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10548,c_52])).

cnf(c_12569,plain,
    ( k2_yellow_0(sK0,X0) = k2_yellow_0(sK2,X0)
    | r2_yellow_0(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12568])).

cnf(c_12771,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7)
    | k2_yellow_0(sK0,sK7) = k2_yellow_0(sK2,sK7) ),
    inference(superposition,[status(thm)],[c_12654,c_12569])).

cnf(c_6,plain,
    ( ~ r4_waybel_0(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_yellow_0(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2)
    | k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r3_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2080,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_24])).

cnf(c_2081,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_2080])).

cnf(c_2083,plain,
    ( r2_yellow_0(sK2,sK7)
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2081,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_2084,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | r2_yellow_0(sK2,sK7) ),
    inference(renaming,[status(thm)],[c_2083])).

cnf(c_3442,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k1_yellow_0(X1,X3))
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_2084])).

cnf(c_3443,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4)
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(unflattening,[status(thm)],[c_3442])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3445,plain,
    ( r2_yellow_0(sK2,sK7)
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3443,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_3446,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | r2_yellow_0(sK2,sK7)
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(renaming,[status(thm)],[c_3445])).

cnf(c_5525,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | r1_yellow_0(sK0,sK6) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3446])).

cnf(c_27,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_471,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(resolution,[status(thm)],[c_10,c_12])).

cnf(c_3592,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_471,c_44])).

cnf(c_3593,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_3592])).

cnf(c_3595,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3593,c_43])).

cnf(c_3570,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_471,c_40])).

cnf(c_3571,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_3570])).

cnf(c_3573,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3571,c_39])).

cnf(c_18,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_491,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X3 = X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK3) != X5
    | u1_struct_0(sK2) != X4
    | sK4 != X0
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_492,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | sK5 = sK4 ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_494,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK3))
    | sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_36,c_35,c_34,c_33,c_32,c_31])).

cnf(c_3615,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK5 = sK4 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3573,c_494])).

cnf(c_3621,plain,
    ( sK5 = sK4 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3595,c_3615])).

cnf(c_5567,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5525,c_27,c_3621])).

cnf(c_7729,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_5567])).

cnf(c_9923,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7729,c_8841])).

cnf(c_37,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_6642,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_5555])).

cnf(c_7001,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK1)
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6642])).

cnf(c_54,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5557,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6640,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_5555])).

cnf(c_6721,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK1)
    | m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6640])).

cnf(c_8398,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK1)
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5557,c_6721])).

cnf(c_8488,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7001,c_54,c_8398])).

cnf(c_9927,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK0,sK7))
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9923,c_8488])).

cnf(c_5547,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5554,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6582,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_5547,c_5554])).

cnf(c_8,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5559,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7763,plain,
    ( m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK2)) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6730,c_5559])).

cnf(c_8749,plain,
    ( m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7763,c_48])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3625,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | u1_struct_0(sK3) != X3
    | u1_struct_0(sK2) != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_3626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_3625])).

cnf(c_1220,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X2)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | u1_struct_0(sK3) != X3
    | u1_struct_0(sK2) != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_1220])).

cnf(c_1225,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1221,c_33,c_31])).

cnf(c_1226,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(renaming,[status(thm)],[c_1225])).

cnf(c_3581,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_471,c_42])).

cnf(c_3582,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_3581])).

cnf(c_3628,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3626,c_41,c_33,c_31,c_1221,c_3582])).

cnf(c_5524,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3628])).

cnf(c_8755,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK0,X0)) = k1_funct_1(sK5,k1_yellow_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_8749,c_5524])).

cnf(c_9928,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9927,c_6582,c_8755])).

cnf(c_19,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r2_yellow_0(X2,X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5553,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r2_yellow_0(X1,X2) != iProver_top
    | r2_yellow_0(X0,X2) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7166,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r2_yellow_0(X0,X1) != iProver_top
    | r2_yellow_0(sK0,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_5553])).

cnf(c_7402,plain,
    ( l1_orders_2(X0) != iProver_top
    | r2_yellow_0(sK0,X1) = iProver_top
    | r2_yellow_0(X0,X1) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7166,c_48])).

cnf(c_7403,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r2_yellow_0(X0,X1) != iProver_top
    | r2_yellow_0(sK0,X1) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7402])).

cnf(c_7408,plain,
    ( r2_yellow_0(sK0,X0) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7403])).

cnf(c_8962,plain,
    ( r2_yellow_0(sK2,X0) != iProver_top
    | r2_yellow_0(sK0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7408,c_52])).

cnf(c_8963,plain,
    ( r2_yellow_0(sK0,X0) = iProver_top
    | r2_yellow_0(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8962])).

cnf(c_9930,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9928,c_8963])).

cnf(c_8081,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | r2_yellow_0(sK0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6928,c_5550])).

cnf(c_8083,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | r2_yellow_0(sK0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8081,c_6730])).

cnf(c_10426,plain,
    ( l1_orders_2(X0) != iProver_top
    | r2_yellow_0(sK0,X1) != iProver_top
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8083,c_48])).

cnf(c_10427,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK0,X1)
    | r2_yellow_0(sK0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10426])).

cnf(c_10434,plain,
    ( k2_yellow_0(sK0,X0) = k2_yellow_0(sK2,X0)
    | r2_yellow_0(sK0,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10427])).

cnf(c_12307,plain,
    ( r2_yellow_0(sK0,X0) != iProver_top
    | k2_yellow_0(sK0,X0) = k2_yellow_0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10434,c_52])).

cnf(c_12308,plain,
    ( k2_yellow_0(sK0,X0) = k2_yellow_0(sK2,X0)
    | r2_yellow_0(sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12307])).

cnf(c_12314,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k2_yellow_0(sK0,sK7) = k2_yellow_0(sK2,sK7) ),
    inference(superposition,[status(thm)],[c_9930,c_12308])).

cnf(c_12979,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k2_yellow_0(sK0,sK7) = k2_yellow_0(sK2,sK7) ),
    inference(superposition,[status(thm)],[c_12771,c_12314])).

cnf(c_6503,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) = k1_funct_1(sK5,k1_yellow_0(sK2,X0))
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5559,c_5524])).

cnf(c_9694,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,X0)) = k1_funct_1(sK5,k1_yellow_0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6503,c_52])).

cnf(c_4,plain,
    ( r4_waybel_0(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2)
    | k1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k1_yellow_0(X0,X3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3242,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k1_yellow_0(X1,X3))
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2098])).

cnf(c_3243,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5)
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(unflattening,[status(thm)],[c_3242])).

cnf(c_3245,plain,
    ( r2_yellow_0(sK2,sK7)
    | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3243,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_3246,plain,
    ( ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r2_yellow_0(sK2,sK7)
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(renaming,[status(thm)],[c_3245])).

cnf(c_5533,plain,
    ( k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7))
    | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3246])).

cnf(c_7131,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5533,c_6582])).

cnf(c_9698,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9694,c_7131])).

cnf(c_7,plain,
    ( ~ r4_waybel_0(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_yellow_0(X0,X3)
    | r1_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3342,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X1,X3)
    | r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_2084])).

cnf(c_3343,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_yellow_0(sK2,sK7)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_3342])).

cnf(c_3345,plain,
    ( r2_yellow_0(sK2,sK7)
    | ~ r1_yellow_0(sK0,sK6)
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3343,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_3346,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | r2_yellow_0(sK2,sK7) ),
    inference(renaming,[status(thm)],[c_3345])).

cnf(c_5529,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = iProver_top
    | r1_yellow_0(sK0,sK6) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3346])).

cnf(c_5565,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5529,c_27,c_3621])).

cnf(c_7731,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_5565])).

cnf(c_9826,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7731,c_8841])).

cnf(c_9830,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9826,c_8488])).

cnf(c_9831,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9830,c_6582])).

cnf(c_7139,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_yellow_0(X0,X1) = iProver_top
    | r1_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_5552])).

cnf(c_50,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_7307,plain,
    ( l1_orders_2(X0) != iProver_top
    | r1_yellow_0(sK1,X1) != iProver_top
    | r1_yellow_0(X0,X1) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7139,c_50])).

cnf(c_7308,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_yellow_0(X0,X1) = iProver_top
    | r1_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7307])).

cnf(c_7315,plain,
    ( r1_yellow_0(sK1,X0) != iProver_top
    | r1_yellow_0(sK3,X0) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7308])).

cnf(c_8844,plain,
    ( r1_yellow_0(sK3,X0) = iProver_top
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7315,c_54])).

cnf(c_8845,plain,
    ( r1_yellow_0(sK1,X0) != iProver_top
    | r1_yellow_0(sK3,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8844])).

cnf(c_9834,plain,
    ( r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9831,c_8845])).

cnf(c_11764,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9698,c_9834])).

cnf(c_13059,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k2_yellow_0(sK0,sK7) = k2_yellow_0(sK2,sK7)
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_12979,c_11764])).

cnf(c_8101,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK1,X1)
    | r1_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_5551])).

cnf(c_8330,plain,
    ( l1_orders_2(X0) != iProver_top
    | r1_yellow_0(sK1,X1) != iProver_top
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK1,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8101,c_50])).

cnf(c_8331,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK1,X1)
    | r1_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8330])).

cnf(c_8339,plain,
    ( k1_yellow_0(sK3,X0) = k1_yellow_0(sK1,X0)
    | r1_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8331])).

cnf(c_9520,plain,
    ( r1_yellow_0(sK1,X0) != iProver_top
    | k1_yellow_0(sK3,X0) = k1_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8339,c_54])).

cnf(c_9521,plain,
    ( k1_yellow_0(sK3,X0) = k1_yellow_0(sK1,X0)
    | r1_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9520])).

cnf(c_9833,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9831,c_9521])).

cnf(c_11687,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9833,c_8963])).

cnf(c_12313,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k2_yellow_0(sK0,sK7) = k2_yellow_0(sK2,sK7) ),
    inference(superposition,[status(thm)],[c_11687,c_12308])).

cnf(c_13394,plain,
    ( k2_yellow_0(sK0,sK7) = k2_yellow_0(sK2,sK7)
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13059,c_12313])).

cnf(c_13398,plain,
    ( k2_yellow_0(sK0,sK7) = k2_yellow_0(sK2,sK7) ),
    inference(superposition,[status(thm)],[c_13394,c_12569])).

cnf(c_2,plain,
    ( ~ r3_waybel_0(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_yellow_0(X0,X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3)) = k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | r3_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2176,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k2_yellow_0(X1,X3)) = k2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_2177,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_2176])).

cnf(c_2179,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2177,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_2180,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_2179])).

cnf(c_3282,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X1,X3)
    | r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_2180])).

cnf(c_3283,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_3282])).

cnf(c_3285,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3283,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_3286,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_3285])).

cnf(c_5532,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = iProver_top
    | r1_yellow_0(sK0,sK6) != iProver_top
    | r2_yellow_0(sK0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3286])).

cnf(c_5571,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5532,c_27,c_3621])).

cnf(c_6207,plain,
    ( ~ r2_yellow_0(X0,sK7)
    | r2_yellow_0(X1,sK7)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_7234,plain,
    ( r2_yellow_0(X0,sK7)
    | ~ r2_yellow_0(sK2,sK7)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(sK2)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_6207])).

cnf(c_7235,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r2_yellow_0(X0,sK7) = iProver_top
    | r2_yellow_0(sK2,sK7) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7234])).

cnf(c_7237,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r2_yellow_0(sK0,sK7) = iProver_top
    | r2_yellow_0(sK2,sK7) != iProver_top
    | l1_orders_2(sK0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7235])).

cnf(c_7645,plain,
    ( r1_yellow_0(sK0,sK7) != iProver_top
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5571,c_48,c_52,c_38,c_5565,c_7237])).

cnf(c_7646,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_7645])).

cnf(c_7649,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7646,c_6730])).

cnf(c_8493,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8488,c_7649])).

cnf(c_8502,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8493,c_6582])).

cnf(c_9,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5558,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7764,plain,
    ( m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK2)) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6730,c_5558])).

cnf(c_9013,plain,
    ( m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7764,c_48])).

cnf(c_9019,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK0,X0)) = k1_funct_1(sK5,k2_yellow_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_9013,c_5524])).

cnf(c_10761,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8502,c_9019])).

cnf(c_25,negated_conjecture,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | r3_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2193,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k2_yellow_0(X1,X3)) = k2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_25])).

cnf(c_2194,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_2193])).

cnf(c_2196,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_2197,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ r2_yellow_0(sK0,sK6)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_2196])).

cnf(c_3094,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_2197])).

cnf(c_3095,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_yellow_0(sK2,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(unflattening,[status(thm)],[c_3094])).

cnf(c_3097,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r1_yellow_0(sK2,sK7)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3095,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_3098,plain,
    ( r1_yellow_0(sK2,sK7)
    | ~ r2_yellow_0(sK0,sK6)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(renaming,[status(thm)],[c_3097])).

cnf(c_5540,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3098])).

cnf(c_5568,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5540,c_27,c_3621])).

cnf(c_7728,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_5568])).

cnf(c_3150,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK2,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3149])).

cnf(c_9913,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7728,c_48,c_52,c_38,c_3150,c_7237])).

cnf(c_9914,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_9913])).

cnf(c_9917,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9914,c_8488])).

cnf(c_9918,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9917,c_6582,c_9019])).

cnf(c_9920,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9918,c_8836])).

cnf(c_10763,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10761,c_9920])).

cnf(c_10764,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10763])).

cnf(c_13408,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13398,c_10764])).

cnf(c_3382,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k1_yellow_0(X1,X3))
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_2180])).

cnf(c_3383,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(unflattening,[status(thm)],[c_3382])).

cnf(c_3385,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK0,sK6)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3383,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_3386,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | ~ r2_yellow_0(sK0,sK6)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(renaming,[status(thm)],[c_3385])).

cnf(c_5528,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | r1_yellow_0(sK0,sK6) != iProver_top
    | r2_yellow_0(sK0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3386])).

cnf(c_5574,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5528,c_27,c_3621])).

cnf(c_7652,plain,
    ( r1_yellow_0(sK0,sK7) != iProver_top
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5574,c_48,c_52,c_38,c_5567,c_7237])).

cnf(c_7653,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_7652])).

cnf(c_7656,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7653,c_6730])).

cnf(c_8492,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8488,c_7656])).

cnf(c_8503,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8492,c_6582])).

cnf(c_10771,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8503,c_8755,c_9019])).

cnf(c_10773,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10771,c_9920])).

cnf(c_10774,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_10773])).

cnf(c_13407,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_13398,c_10774])).

cnf(c_3,plain,
    ( ~ r3_waybel_0(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_yellow_0(X0,X3)
    | r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2159,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(X1,X3)
    | r2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_2160,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_2159])).

cnf(c_2162,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2160,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_2163,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(renaming,[status(thm)],[c_2162])).

cnf(c_3111,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_2163])).

cnf(c_3112,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_yellow_0(sK2,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_3111])).

cnf(c_3114,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | r1_yellow_0(sK2,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3112,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_3115,plain,
    ( r1_yellow_0(sK2,sK7)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(renaming,[status(thm)],[c_3114])).

cnf(c_5539,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = iProver_top
    | r2_yellow_0(sK0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3115])).

cnf(c_5566,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5539,c_27,c_3621])).

cnf(c_7730,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_5566])).

cnf(c_9814,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7730,c_48,c_52,c_38,c_3150,c_7237])).

cnf(c_9815,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9814])).

cnf(c_9818,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9815,c_8488])).

cnf(c_9819,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9818,c_6582])).

cnf(c_7167,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r2_yellow_0(X0,X1) = iProver_top
    | r2_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_5553])).

cnf(c_7487,plain,
    ( l1_orders_2(X0) != iProver_top
    | r2_yellow_0(sK1,X1) != iProver_top
    | r2_yellow_0(X0,X1) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7167,c_50])).

cnf(c_7488,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r2_yellow_0(X0,X1) = iProver_top
    | r2_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7487])).

cnf(c_7495,plain,
    ( r2_yellow_0(sK1,X0) != iProver_top
    | r2_yellow_0(sK3,X0) = iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_7488])).

cnf(c_9222,plain,
    ( r2_yellow_0(sK3,X0) = iProver_top
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7495,c_54])).

cnf(c_9223,plain,
    ( r2_yellow_0(sK1,X0) != iProver_top
    | r2_yellow_0(sK3,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9222])).

cnf(c_9822,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9819,c_9223])).

cnf(c_12653,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7) ),
    inference(superposition,[status(thm)],[c_9920,c_12647])).

cnf(c_13402,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7) ),
    inference(demodulation,[status(thm)],[c_13398,c_12653])).

cnf(c_0,plain,
    ( r3_waybel_0(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | ~ v1_funct_1(X2)
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_yellow_0(X0,X3)) != k2_yellow_0(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2108,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k2_yellow_0(X1,X3)) != k2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_2109,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(unflattening,[status(thm)],[c_2108])).

cnf(c_2111,plain,
    ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r4_waybel_0(sK0,sK1,sK4,sK6)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2109,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_2112,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_2111])).

cnf(c_3322,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X1,X3)
    | r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_2112])).

cnf(c_3323,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(unflattening,[status(thm)],[c_3322])).

cnf(c_3325,plain,
    ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ r1_yellow_0(sK0,sK6)
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3323,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_3326,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_3325])).

cnf(c_5530,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = iProver_top
    | r1_yellow_0(sK0,sK6) != iProver_top
    | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3326])).

cnf(c_5572,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5530,c_27,c_3621])).

cnf(c_7735,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_5572])).

cnf(c_7739,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7735,c_6582])).

cnf(c_6215,plain,
    ( ~ r1_yellow_0(X0,sK7)
    | r1_yellow_0(X1,sK7)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_8297,plain,
    ( r1_yellow_0(X0,sK7)
    | ~ r1_yellow_0(sK2,sK7)
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(sK2)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(instantiation,[status(thm)],[c_6215])).

cnf(c_8301,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r1_yellow_0(X0,sK7) = iProver_top
    | r1_yellow_0(sK2,sK7) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8297])).

cnf(c_8303,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | r1_yellow_0(sK0,sK7) = iProver_top
    | r1_yellow_0(sK2,sK7) != iProver_top
    | l1_orders_2(sK0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8301])).

cnf(c_2125,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k2_yellow_0(X1,X3)) != k2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_2126,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(unflattening,[status(thm)],[c_2125])).

cnf(c_2128,plain,
    ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2126,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_2129,plain,
    ( ~ r4_waybel_0(sK2,sK3,sK5,sK7)
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_2128])).

cnf(c_3128,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_2129])).

cnf(c_3129,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | r1_yellow_0(sK2,sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(unflattening,[status(thm)],[c_3128])).

cnf(c_3131,plain,
    ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r1_yellow_0(sK2,sK7)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3129,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_3132,plain,
    ( r1_yellow_0(sK2,sK7)
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_3131])).

cnf(c_5538,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3132])).

cnf(c_8627,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5538,c_6582])).

cnf(c_10132,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7739,c_48,c_52,c_38,c_8303,c_8627])).

cnf(c_10133,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10132])).

cnf(c_10136,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10133,c_8488])).

cnf(c_6504,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X0)) = k1_funct_1(sK5,k2_yellow_0(sK2,X0))
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5558,c_5524])).

cnf(c_9702,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,X0)) = k1_funct_1(sK5,k2_yellow_0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6504,c_52])).

cnf(c_10137,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10136,c_6582,c_9702])).

cnf(c_13558,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7)
    | k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13402,c_10137])).

cnf(c_8079,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK1,X1)
    | r2_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_37,c_5550])).

cnf(c_8230,plain,
    ( l1_orders_2(X0) != iProver_top
    | r2_yellow_0(sK1,X1) != iProver_top
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK1,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8079,c_50])).

cnf(c_8231,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | k2_yellow_0(X0,X1) = k2_yellow_0(sK1,X1)
    | r2_yellow_0(sK1,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8230])).

cnf(c_8239,plain,
    ( k2_yellow_0(sK3,X0) = k2_yellow_0(sK1,X0)
    | r2_yellow_0(sK1,X0) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8231])).

cnf(c_9412,plain,
    ( r2_yellow_0(sK1,X0) != iProver_top
    | k2_yellow_0(sK3,X0) = k2_yellow_0(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8239,c_54])).

cnf(c_9413,plain,
    ( k2_yellow_0(sK3,X0) = k2_yellow_0(sK1,X0)
    | r2_yellow_0(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9412])).

cnf(c_9821,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9819,c_9413])).

cnf(c_11365,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9821,c_8836])).

cnf(c_12652,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7)
    | k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_11365,c_12647])).

cnf(c_13999,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7)
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13558,c_12652])).

cnf(c_14005,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7)
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9822,c_13999])).

cnf(c_9705,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9702,c_8627])).

cnf(c_11899,plain,
    ( r1_yellow_0(sK2,sK7) = iProver_top
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9705,c_9822])).

cnf(c_11900,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_11899])).

cnf(c_13556,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7)
    | k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_13402,c_11900])).

cnf(c_14051,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7)
    | r1_yellow_0(sK2,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14005,c_12652,c_13556])).

cnf(c_8100,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK0,X1)
    | r1_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6928,c_5551])).

cnf(c_8107,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK0,X1)
    | r1_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8100,c_6730])).

cnf(c_10873,plain,
    ( l1_orders_2(X0) != iProver_top
    | r1_yellow_0(X0,X1) != iProver_top
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8107,c_48])).

cnf(c_10874,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
    | k1_yellow_0(X0,X1) = k1_yellow_0(sK0,X1)
    | r1_yellow_0(X0,X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10873])).

cnf(c_10881,plain,
    ( k1_yellow_0(sK0,X0) = k1_yellow_0(sK2,X0)
    | r1_yellow_0(sK2,X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10874])).

cnf(c_12657,plain,
    ( r1_yellow_0(sK2,X0) != iProver_top
    | k1_yellow_0(sK0,X0) = k1_yellow_0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10881,c_52])).

cnf(c_12658,plain,
    ( k1_yellow_0(sK0,X0) = k1_yellow_0(sK2,X0)
    | r1_yellow_0(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12657])).

cnf(c_14055,plain,
    ( k1_yellow_0(sK0,sK7) = k1_yellow_0(sK2,sK7) ),
    inference(superposition,[status(thm)],[c_14051,c_12658])).

cnf(c_14060,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_13407,c_14055])).

cnf(c_3182,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k1_yellow_0(X1,X3))
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2197])).

cnf(c_3183,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(unflattening,[status(thm)],[c_3182])).

cnf(c_3185,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3183,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_3186,plain,
    ( ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ r2_yellow_0(sK0,sK6)
    | k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(renaming,[status(thm)],[c_3185])).

cnf(c_5536,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k2_yellow_0(sK0,sK6)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7))
    | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top
    | r2_yellow_0(sK0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3186])).

cnf(c_5576,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7))
    | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5536,c_27,c_3621])).

cnf(c_7732,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7))
    | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_5576])).

cnf(c_7742,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7732,c_6582])).

cnf(c_11018,plain,
    ( r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7742,c_48,c_52,c_38,c_7131,c_7237])).

cnf(c_11019,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11018])).

cnf(c_11022,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11019,c_8488])).

cnf(c_11023,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11022,c_6582,c_9019,c_9694])).

cnf(c_10768,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10764,c_8845])).

cnf(c_11025,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11023,c_10768])).

cnf(c_11026,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_11025])).

cnf(c_13406,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_13398,c_11026])).

cnf(c_14061,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_14060,c_13406])).

cnf(c_10767,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK0,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_10764,c_9521])).

cnf(c_13403,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_13398,c_10767])).

cnf(c_13722,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13403,c_10137])).

cnf(c_2142,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(X1,X3)
    | r2_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_2143,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_2142])).

cnf(c_2145,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | r4_waybel_0(sK0,sK1,sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2143,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_2146,plain,
    ( r4_waybel_0(sK0,sK1,sK4,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(renaming,[status(thm)],[c_2145])).

cnf(c_3302,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X1,X3)
    | r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_2146])).

cnf(c_3303,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_3302])).

cnf(c_3305,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3303,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_3306,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6) ),
    inference(renaming,[status(thm)],[c_3305])).

cnf(c_5531,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = iProver_top
    | r1_yellow_0(sK0,sK6) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = iProver_top
    | r2_yellow_0(sK0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3306])).

cnf(c_5569,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5531,c_27,c_3621])).

cnf(c_7179,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5569,c_6730])).

cnf(c_8495,plain,
    ( r1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8488,c_7179])).

cnf(c_8500,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8495,c_6582])).

cnf(c_10209,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8500,c_48,c_52,c_38,c_7237,c_8303,c_9819,c_9831])).

cnf(c_10210,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10209])).

cnf(c_10213,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10210,c_9521])).

cnf(c_12003,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_10213,c_9413])).

cnf(c_12004,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10213,c_9223])).

cnf(c_14177,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13722,c_12003,c_12004])).

cnf(c_14178,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_14177])).

cnf(c_14181,plain,
    ( k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_14178,c_9521])).

cnf(c_14430,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13408,c_14061,c_14181])).

cnf(c_3402,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k1_yellow_0(X1,X3))
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_2146])).

cnf(c_3403,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4)
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(unflattening,[status(thm)],[c_3402])).

cnf(c_3405,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3403,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_3406,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(renaming,[status(thm)],[c_3405])).

cnf(c_5527,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | r1_yellow_0(sK0,sK6) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = iProver_top
    | r2_yellow_0(sK0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3406])).

cnf(c_5570,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5527,c_27,c_3621])).

cnf(c_7578,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK0,sK7) != iProver_top
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5570,c_48,c_52,c_38,c_5567,c_7237])).

cnf(c_7579,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7578])).

cnf(c_7582,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7579,c_6730])).

cnf(c_8494,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8488,c_7582])).

cnf(c_8501,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8494,c_6582])).

cnf(c_10651,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8501,c_48,c_52,c_38,c_8303,c_9819])).

cnf(c_10655,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10651,c_8755])).

cnf(c_14189,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14055,c_10655])).

cnf(c_14192,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14189,c_14181])).

cnf(c_3202,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k1_yellow_0(X1,X3))
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2163])).

cnf(c_3203,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5)
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(unflattening,[status(thm)],[c_3202])).

cnf(c_3205,plain,
    ( ~ r2_yellow_0(sK0,sK6)
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3203,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_3206,plain,
    ( ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6))
    | ~ r2_yellow_0(sK0,sK6)
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(renaming,[status(thm)],[c_3205])).

cnf(c_5535,plain,
    ( k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7))
    | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = iProver_top
    | r2_yellow_0(sK0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3206])).

cnf(c_5573,plain,
    ( k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7))
    | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5535,c_27,c_3621])).

cnf(c_7734,plain,
    ( k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7))
    | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_5573])).

cnf(c_7740,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r2_yellow_0(sK0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7734,c_6582])).

cnf(c_10639,plain,
    ( r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7740,c_48,c_52,c_38,c_7131,c_7237])).

cnf(c_10640,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10639])).

cnf(c_10643,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10640,c_8488])).

cnf(c_10644,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10643,c_6582,c_9694])).

cnf(c_10214,plain,
    ( r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10210,c_8845])).

cnf(c_10646,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10644,c_10214])).

cnf(c_14358,plain,
    ( r2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14192,c_10646])).

cnf(c_14362,plain,
    ( k2_yellow_0(sK1,k9_relat_1(sK5,sK7)) = k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_14358,c_9413])).

cnf(c_14432,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) = k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_14430,c_14362])).

cnf(c_14436,plain,
    ( k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14432,c_10137])).

cnf(c_14437,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14436])).

cnf(c_14363,plain,
    ( r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14358,c_9223])).

cnf(c_14492,plain,
    ( r1_yellow_0(sK1,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14437,c_10137,c_14363,c_14432])).

cnf(c_14497,plain,
    ( r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14492,c_8845])).

cnf(c_3422,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k1_yellow_0(X1,X3))
    | sK6 != X3
    | sK4 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_2112])).

cnf(c_3423,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK0,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v1_funct_1(sK4)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(unflattening,[status(thm)],[c_3422])).

cnf(c_3425,plain,
    ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ r1_yellow_0(sK0,sK6)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3423,c_46,c_45,c_44,c_43,c_36,c_35,c_34,c_29])).

cnf(c_3426,plain,
    ( ~ r1_yellow_0(sK0,sK6)
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6)) ),
    inference(renaming,[status(thm)],[c_3425])).

cnf(c_5526,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k1_yellow_0(sK0,sK6))
    | r1_yellow_0(sK0,sK6) != iProver_top
    | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3426])).

cnf(c_5575,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5526,c_27,c_3621])).

cnf(c_7733,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_5575])).

cnf(c_7741,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r1_yellow_0(sK0,sK7) != iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7733,c_6582])).

cnf(c_10888,plain,
    ( k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7741,c_48,c_52,c_38,c_8303,c_8627])).

cnf(c_10889,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK5,k1_yellow_0(sK0,sK7))
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10888])).

cnf(c_10892,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_yellow_0(sK1,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK0,sK7))
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10889,c_8488])).

cnf(c_10893,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10892,c_6582,c_8755,c_9702])).

cnf(c_10658,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10655,c_9223])).

cnf(c_10895,plain,
    ( k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10893,c_10658])).

cnf(c_10896,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK0,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(renaming,[status(thm)],[c_10895])).

cnf(c_14188,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) = k1_yellow_0(sK1,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_14055,c_10896])).

cnf(c_14193,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) = k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7)) ),
    inference(light_normalisation,[status(thm)],[c_14188,c_14181])).

cnf(c_3222,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(X2,k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,k1_yellow_0(X1,X3))
    | sK7 != X3
    | sK5 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2129])).

cnf(c_3223,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2)
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(unflattening,[status(thm)],[c_3222])).

cnf(c_3225,plain,
    ( ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3223,c_42,c_41,c_40,c_39,c_33,c_32,c_31,c_28])).

cnf(c_3226,plain,
    ( ~ r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | ~ r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) ),
    inference(renaming,[status(thm)],[c_3225])).

cnf(c_5534,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7))
    | k1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7))
    | r1_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top
    | r2_yellow_0(sK3,k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3226])).

cnf(c_7399,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5534,c_6582])).

cnf(c_9697,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9694,c_7399])).

cnf(c_12205,plain,
    ( k1_funct_1(sK5,k1_yellow_0(sK2,sK7)) != k1_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | k1_funct_1(sK5,k2_yellow_0(sK2,sK7)) != k2_yellow_0(sK3,k9_relat_1(sK5,sK7))
    | r1_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top
    | r2_yellow_0(sK3,k9_relat_1(sK5,sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9697,c_9702])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14497,c_14432,c_14363,c_14193,c_12205])).


%------------------------------------------------------------------------------
