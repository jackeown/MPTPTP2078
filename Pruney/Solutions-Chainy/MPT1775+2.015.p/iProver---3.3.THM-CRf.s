%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:20 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 964 expanded)
%              Number of clauses        :  131 ( 183 expanded)
%              Number of leaves         :   22 ( 390 expanded)
%              Depth                    :   27
%              Number of atoms          : 1745 (17161 expanded)
%              Number of equality atoms :  289 (1240 expanded)
%              Maximal formula depth    :   31 (   8 average)
%              Maximal clause size      :   44 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X1,X4,X5) )
          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            | r1_tmap_1(X3,X1,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
          | ~ r1_tmap_1(X3,X1,X4,X5) )
        & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
          | r1_tmap_1(X3,X1,X4,X5) )
        & sK8 = X5
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                | ~ r1_tmap_1(X3,X1,X4,X5) )
              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                | r1_tmap_1(X3,X1,X4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | ~ r1_tmap_1(X3,X1,X4,sK7) )
            & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              | r1_tmap_1(X3,X1,X4,sK7) )
            & sK7 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                    | ~ r1_tmap_1(X3,X1,X4,X5) )
                  & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                    | r1_tmap_1(X3,X1,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & v1_tsep_1(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X6)
                  | ~ r1_tmap_1(X3,X1,sK6,X5) )
                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X6)
                  | r1_tmap_1(X3,X1,sK6,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & v1_tsep_1(X2,X3)
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                        | ~ r1_tmap_1(X3,X1,X4,X5) )
                      & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                        | r1_tmap_1(X3,X1,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & v1_tsep_1(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X6)
                      | ~ r1_tmap_1(sK5,X1,X4,X5) )
                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X6)
                      | r1_tmap_1(sK5,X1,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK5)) )
            & m1_pre_topc(X2,sK5)
            & v1_tsep_1(X2,sK5)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,X1,X4,X5) )
                          & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                            | r1_tmap_1(X3,X1,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X6)
                          | ~ r1_tmap_1(X3,X1,X4,X5) )
                        & ( r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X6)
                          | r1_tmap_1(X3,X1,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK4)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK4,X3)
                & v1_tsep_1(sK4,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK3,X4,X5) )
                            & ( r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK3,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X1,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & v1_tsep_1(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
      | ~ r1_tmap_1(sK5,sK3,sK6,sK7) )
    & ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
      | r1_tmap_1(sK5,sK3,sK6,sK7) )
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_pre_topc(sK4,sK5)
    & v1_tsep_1(sK4,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f44,f51,f50,f49,f48,f47,f46,f45])).

fof(f83,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK1(X0,X1,X4),X1)
        & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK0(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK1(X0,X1,X4),X1)
                    & m1_connsp_2(sK1(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f52])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK1(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    v1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

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

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,
    ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_16,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_16])).

cnf(c_204,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_938,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_27])).

cnf(c_939,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | ~ r1_tmap_1(X3,X1,sK6,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_938])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_943,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tmap_1(X3,X1,sK6,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_939,c_28])).

cnf(c_944,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | ~ r1_tmap_1(X3,X1,sK6,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_943])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_985,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | ~ r1_tmap_1(X3,X1,sK6,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_944,c_15])).

cnf(c_2300,plain,
    ( r1_tmap_1(X0_56,X1_56,k3_tmap_1(X2_56,X1_56,X3_56,X0_56,sK6),X0_57)
    | ~ r1_tmap_1(X3_56,X1_56,sK6,X0_57)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_subset_1(X0_57,u1_struct_0(X3_56))
    | ~ m1_subset_1(X0_57,u1_struct_0(X0_56))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X1_56))))
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | u1_struct_0(X3_56) != u1_struct_0(sK5)
    | u1_struct_0(X1_56) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_985])).

cnf(c_3406,plain,
    ( r1_tmap_1(X0_56,X1_56,k3_tmap_1(X2_56,X1_56,sK5,X0_56,sK6),X0_57)
    | ~ r1_tmap_1(sK5,X1_56,sK6,X0_57)
    | ~ m1_pre_topc(X0_56,sK5)
    | ~ m1_pre_topc(sK5,X2_56)
    | ~ m1_subset_1(X0_57,u1_struct_0(X0_56))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56))))
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | u1_struct_0(X1_56) != u1_struct_0(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2300])).

cnf(c_3793,plain,
    ( ~ r1_tmap_1(sK5,X0_56,sK6,X0_57)
    | r1_tmap_1(sK4,X0_56,k3_tmap_1(X1_56,X0_56,sK5,sK4,sK6),X0_57)
    | ~ m1_pre_topc(sK5,X1_56)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X0_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | u1_struct_0(X0_56) != u1_struct_0(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3406])).

cnf(c_3833,plain,
    ( ~ r1_tmap_1(sK5,X0_56,sK6,X0_57)
    | r1_tmap_1(sK4,X0_56,k3_tmap_1(sK2,X0_56,sK5,sK4,sK6),X0_57)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X0_56) != u1_struct_0(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3793])).

cnf(c_4741,plain,
    ( ~ r1_tmap_1(sK5,X0_56,sK6,sK8)
    | r1_tmap_1(sK4,X0_56,k3_tmap_1(sK2,X0_56,sK5,sK4,sK6),sK8)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
    | v2_struct_0(X0_56)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0_56)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X0_56) != u1_struct_0(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3833])).

cnf(c_4743,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK8)
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v2_struct_0(sK5)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4741])).

cnf(c_8,plain,
    ( r1_tarski(sK1(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2325,plain,
    ( r1_tarski(sK1(X0_56,X0_57,X1_57),X0_57)
    | ~ v3_pre_topc(X0_57,X0_56)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_56)))
    | ~ m1_subset_1(X1_57,u1_struct_0(X0_56))
    | ~ r2_hidden(X1_57,X0_57)
    | v2_struct_0(X0_56)
    | ~ l1_pre_topc(X0_56)
    | ~ v2_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3068,plain,
    ( r1_tarski(sK1(X0_56,X0_57,X1_57),X0_57) = iProver_top
    | v3_pre_topc(X0_57,X0_56) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
    | r2_hidden(X1_57,X0_57) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2325])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK5,sK3,sK6,sK7)
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2320,negated_conjecture,
    ( r1_tmap_1(sK5,sK3,sK6,sK7)
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3073,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK7) = iProver_top
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2320])).

cnf(c_21,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2319,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3148,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3073,c_2319])).

cnf(c_9,plain,
    ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X6,X0,X3)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_700,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v3_pre_topc(X7,X8)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X9,u1_struct_0(X8))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r2_hidden(X9,X7)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X8)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X8)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X8)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | X0 != X8
    | X3 != X9
    | sK1(X8,X7,X9) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_701,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(sK1(X0,X6,X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_755,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r2_hidden(X3,X6)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_701,c_1,c_3,c_10,c_15])).

cnf(c_884,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r2_hidden(X3,X6)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_755,c_27])).

cnf(c_885,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | r1_tmap_1(X3,X1,sK6,X4)
    | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_889,plain,
    ( ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ v3_pre_topc(X5,X3)
    | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
    | r1_tmap_1(X3,X1,sK6,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_885,c_28])).

cnf(c_890,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
    | r1_tmap_1(X3,X1,sK6,X4)
    | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_889])).

cnf(c_2301,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,k3_tmap_1(X2_56,X1_56,X3_56,X0_56,sK6),X0_57)
    | r1_tmap_1(X3_56,X1_56,sK6,X0_57)
    | ~ r1_tarski(sK1(X3_56,X1_57,X0_57),u1_struct_0(X0_56))
    | ~ v3_pre_topc(X1_57,X3_56)
    | ~ m1_pre_topc(X0_56,X3_56)
    | ~ m1_pre_topc(X3_56,X2_56)
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X3_56)))
    | ~ m1_subset_1(X0_57,u1_struct_0(X3_56))
    | ~ m1_subset_1(X0_57,u1_struct_0(X0_56))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X1_56))))
    | ~ r2_hidden(X0_57,X1_57)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | v2_struct_0(X2_56)
    | v2_struct_0(X3_56)
    | ~ l1_pre_topc(X1_56)
    | ~ l1_pre_topc(X2_56)
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X2_56)
    | u1_struct_0(X3_56) != u1_struct_0(sK5)
    | u1_struct_0(X1_56) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_890])).

cnf(c_3091,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK5)
    | u1_struct_0(X1_56) != u1_struct_0(sK3)
    | r1_tmap_1(X2_56,X1_56,k3_tmap_1(X3_56,X1_56,X0_56,X2_56,sK6),X0_57) != iProver_top
    | r1_tmap_1(X0_56,X1_56,sK6,X0_57) = iProver_top
    | r1_tarski(sK1(X0_56,X1_57,X0_57),u1_struct_0(X2_56)) != iProver_top
    | v3_pre_topc(X1_57,X0_56) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_pre_topc(X0_56,X3_56) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X2_56)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | r2_hidden(X0_57,X1_57) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X3_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X3_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X3_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2301])).

cnf(c_4525,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK5)
    | r1_tmap_1(X1_56,sK3,k3_tmap_1(X2_56,sK3,X0_56,X1_56,sK6),X0_57) != iProver_top
    | r1_tmap_1(X0_56,sK3,sK6,X0_57) = iProver_top
    | r1_tarski(sK1(X0_56,X1_57,X0_57),u1_struct_0(X1_56)) != iProver_top
    | v3_pre_topc(X1_57,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(X0_57,X1_57) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3091])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_44,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4594,plain,
    ( v2_pre_topc(X2_56) != iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | r2_hidden(X0_57,X1_57) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | v3_pre_topc(X1_57,X0_56) != iProver_top
    | r1_tarski(sK1(X0_56,X1_57,X0_57),u1_struct_0(X1_56)) != iProver_top
    | r1_tmap_1(X0_56,sK3,sK6,X0_57) = iProver_top
    | r1_tmap_1(X1_56,sK3,k3_tmap_1(X2_56,sK3,X0_56,X1_56,sK6),X0_57) != iProver_top
    | u1_struct_0(X0_56) != u1_struct_0(sK5)
    | l1_pre_topc(X2_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4525,c_42,c_43,c_44])).

cnf(c_4595,plain,
    ( u1_struct_0(X0_56) != u1_struct_0(sK5)
    | r1_tmap_1(X1_56,sK3,k3_tmap_1(X2_56,sK3,X0_56,X1_56,sK6),X0_57) != iProver_top
    | r1_tmap_1(X0_56,sK3,sK6,X0_57) = iProver_top
    | r1_tarski(sK1(X0_56,X1_57,X0_57),u1_struct_0(X1_56)) != iProver_top
    | v3_pre_topc(X1_57,X0_56) != iProver_top
    | m1_pre_topc(X1_56,X0_56) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X1_56)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(X0_57,X1_57) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X2_56) = iProver_top
    | l1_pre_topc(X2_56) != iProver_top
    | v2_pre_topc(X2_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_4594])).

cnf(c_4615,plain,
    ( r1_tmap_1(X0_56,sK3,k3_tmap_1(X1_56,sK3,sK5,X0_56,sK6),X0_57) != iProver_top
    | r1_tmap_1(sK5,sK3,sK6,X0_57) = iProver_top
    | r1_tarski(sK1(sK5,X1_57,X0_57),u1_struct_0(X0_56)) != iProver_top
    | v3_pre_topc(X1_57,sK5) != iProver_top
    | m1_pre_topc(X0_56,sK5) != iProver_top
    | m1_pre_topc(sK5,X1_56) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(X0_57,X1_57) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4595])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_51,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4675,plain,
    ( v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | r2_hidden(X0_57,X1_57) != iProver_top
    | r1_tmap_1(X0_56,sK3,k3_tmap_1(X1_56,sK3,sK5,X0_56,sK6),X0_57) != iProver_top
    | r1_tmap_1(sK5,sK3,sK6,X0_57) = iProver_top
    | r1_tarski(sK1(sK5,X1_57,X0_57),u1_struct_0(X0_56)) != iProver_top
    | v3_pre_topc(X1_57,sK5) != iProver_top
    | m1_pre_topc(X0_56,sK5) != iProver_top
    | m1_pre_topc(sK5,X1_56) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK5)) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4615,c_47,c_51])).

cnf(c_4676,plain,
    ( r1_tmap_1(X0_56,sK3,k3_tmap_1(X1_56,sK3,sK5,X0_56,sK6),X0_57) != iProver_top
    | r1_tmap_1(sK5,sK3,sK6,X0_57) = iProver_top
    | r1_tarski(sK1(sK5,X1_57,X0_57),u1_struct_0(X0_56)) != iProver_top
    | v3_pre_topc(X1_57,sK5) != iProver_top
    | m1_pre_topc(X0_56,sK5) != iProver_top
    | m1_pre_topc(sK5,X1_56) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
    | m1_subset_1(X0_57,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(X0_57,X1_57) != iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_4675])).

cnf(c_4695,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
    | r1_tarski(sK1(sK5,X0_57,sK8),u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_57,sK5) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK8,X0_57) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3148,c_4676])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_40,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_41,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_48,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_53,plain,
    ( m1_pre_topc(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_55,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2317,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3075,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2317])).

cnf(c_3119,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3075,c_2319])).

cnf(c_4700,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
    | r1_tarski(sK1(sK5,X0_57,sK8),u1_struct_0(sK4)) != iProver_top
    | v3_pre_topc(X0_57,sK5) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK8,X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4695,c_39,c_40,c_41,c_45,c_48,c_53,c_55,c_3119])).

cnf(c_4711,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
    | v3_pre_topc(u1_struct_0(sK4),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK8,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3068,c_4700])).

cnf(c_4712,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK8)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK5)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK5))
    | ~ r2_hidden(sK8,u1_struct_0(sK4))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4711])).

cnf(c_2332,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_4380,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_2316,negated_conjecture,
    ( m1_pre_topc(sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3076,plain,
    ( m1_pre_topc(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2316])).

cnf(c_2328,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ l1_pre_topc(X1_56)
    | l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3065,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2328])).

cnf(c_3879,plain,
    ( l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3076,c_3065])).

cnf(c_3894,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3879])).

cnf(c_2314,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3078,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2314])).

cnf(c_2329,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ l1_pre_topc(X1_56)
    | ~ v2_pre_topc(X1_56)
    | v2_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3064,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2329])).

cnf(c_3852,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK5) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_3064])).

cnf(c_3873,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3852])).

cnf(c_13,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_212,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_213,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_25,negated_conjecture,
    ( v1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_536,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_213,c_25])).

cnf(c_537,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK5)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_539,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_24])).

cnf(c_2303,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(subtyping,[status(esa)],[c_539])).

cnf(c_3089,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2303])).

cnf(c_538,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK5) = iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_3416,plain,
    ( ~ m1_pre_topc(sK5,X0_56)
    | ~ l1_pre_topc(X0_56)
    | l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2328])).

cnf(c_3725,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3416])).

cnf(c_3726,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3725])).

cnf(c_3804,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3089,c_41,c_48,c_53,c_538,c_3726])).

cnf(c_3806,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3804])).

cnf(c_2318,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3074,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2318])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2330,plain,
    ( ~ m1_subset_1(X0_57,X1_57)
    | r2_hidden(X0_57,X1_57)
    | v1_xboole_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3063,plain,
    ( m1_subset_1(X0_57,X1_57) != iProver_top
    | r2_hidden(X0_57,X1_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2330])).

cnf(c_3715,plain,
    ( r2_hidden(sK8,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3074,c_3063])).

cnf(c_3716,plain,
    ( r2_hidden(sK8,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3715])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_495,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_2304,plain,
    ( v2_struct_0(X0_56)
    | ~ l1_pre_topc(X0_56)
    | ~ v1_xboole_0(u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_495])).

cnf(c_3526,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_2323,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | m1_subset_1(u1_struct_0(X0_56),k1_zfmisc_1(u1_struct_0(X1_56)))
    | ~ l1_pre_topc(X1_56) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3421,plain,
    ( ~ m1_pre_topc(sK4,sK5)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2323])).

cnf(c_3405,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_3347,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3119])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2321,negated_conjecture,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_3072,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK7) != iProver_top
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2321])).

cnf(c_3159,plain,
    ( r1_tmap_1(sK5,sK3,sK6,sK8) != iProver_top
    | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3072,c_2319])).

cnf(c_3333,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK8)
    | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3159])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4743,c_4712,c_4380,c_3894,c_3873,c_3806,c_3725,c_3716,c_3526,c_3421,c_3405,c_3347,c_3333,c_22,c_24,c_26,c_29,c_30,c_32,c_33,c_34,c_35,c_36,c_37,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.14/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/0.98  
% 2.14/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.14/0.98  
% 2.14/0.98  ------  iProver source info
% 2.14/0.98  
% 2.14/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.14/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.14/0.98  git: non_committed_changes: false
% 2.14/0.98  git: last_make_outside_of_git: false
% 2.14/0.98  
% 2.14/0.98  ------ 
% 2.14/0.98  
% 2.14/0.98  ------ Input Options
% 2.14/0.98  
% 2.14/0.98  --out_options                           all
% 2.14/0.98  --tptp_safe_out                         true
% 2.14/0.98  --problem_path                          ""
% 2.14/0.98  --include_path                          ""
% 2.14/0.98  --clausifier                            res/vclausify_rel
% 2.14/0.98  --clausifier_options                    --mode clausify
% 2.14/0.98  --stdin                                 false
% 2.14/0.98  --stats_out                             all
% 2.14/0.98  
% 2.14/0.98  ------ General Options
% 2.14/0.98  
% 2.14/0.98  --fof                                   false
% 2.14/0.98  --time_out_real                         305.
% 2.14/0.98  --time_out_virtual                      -1.
% 2.14/0.98  --symbol_type_check                     false
% 2.14/0.98  --clausify_out                          false
% 2.14/0.98  --sig_cnt_out                           false
% 2.14/0.98  --trig_cnt_out                          false
% 2.14/0.98  --trig_cnt_out_tolerance                1.
% 2.14/0.98  --trig_cnt_out_sk_spl                   false
% 2.14/0.98  --abstr_cl_out                          false
% 2.14/0.98  
% 2.14/0.98  ------ Global Options
% 2.14/0.98  
% 2.14/0.98  --schedule                              default
% 2.14/0.98  --add_important_lit                     false
% 2.14/0.98  --prop_solver_per_cl                    1000
% 2.14/0.98  --min_unsat_core                        false
% 2.14/0.98  --soft_assumptions                      false
% 2.14/0.98  --soft_lemma_size                       3
% 2.14/0.98  --prop_impl_unit_size                   0
% 2.14/0.98  --prop_impl_unit                        []
% 2.14/0.98  --share_sel_clauses                     true
% 2.14/0.98  --reset_solvers                         false
% 2.14/0.98  --bc_imp_inh                            [conj_cone]
% 2.14/0.98  --conj_cone_tolerance                   3.
% 2.14/0.98  --extra_neg_conj                        none
% 2.14/0.98  --large_theory_mode                     true
% 2.14/0.98  --prolific_symb_bound                   200
% 2.14/0.98  --lt_threshold                          2000
% 2.14/0.98  --clause_weak_htbl                      true
% 2.14/0.98  --gc_record_bc_elim                     false
% 2.14/0.98  
% 2.14/0.98  ------ Preprocessing Options
% 2.14/0.98  
% 2.14/0.98  --preprocessing_flag                    true
% 2.14/0.98  --time_out_prep_mult                    0.1
% 2.14/0.98  --splitting_mode                        input
% 2.14/0.98  --splitting_grd                         true
% 2.14/0.98  --splitting_cvd                         false
% 2.14/0.98  --splitting_cvd_svl                     false
% 2.14/0.98  --splitting_nvd                         32
% 2.14/0.98  --sub_typing                            true
% 2.14/0.98  --prep_gs_sim                           true
% 2.14/0.98  --prep_unflatten                        true
% 2.14/0.98  --prep_res_sim                          true
% 2.14/0.98  --prep_upred                            true
% 2.14/0.98  --prep_sem_filter                       exhaustive
% 2.14/0.98  --prep_sem_filter_out                   false
% 2.14/0.98  --pred_elim                             true
% 2.14/0.98  --res_sim_input                         true
% 2.14/0.98  --eq_ax_congr_red                       true
% 2.14/0.98  --pure_diseq_elim                       true
% 2.14/0.98  --brand_transform                       false
% 2.14/0.98  --non_eq_to_eq                          false
% 2.14/0.98  --prep_def_merge                        true
% 2.14/0.98  --prep_def_merge_prop_impl              false
% 2.14/0.98  --prep_def_merge_mbd                    true
% 2.14/0.98  --prep_def_merge_tr_red                 false
% 2.14/0.98  --prep_def_merge_tr_cl                  false
% 2.14/0.98  --smt_preprocessing                     true
% 2.14/0.98  --smt_ac_axioms                         fast
% 2.14/0.98  --preprocessed_out                      false
% 2.14/0.98  --preprocessed_stats                    false
% 2.14/0.98  
% 2.14/0.98  ------ Abstraction refinement Options
% 2.14/0.98  
% 2.14/0.98  --abstr_ref                             []
% 2.14/0.98  --abstr_ref_prep                        false
% 2.14/0.98  --abstr_ref_until_sat                   false
% 2.14/0.98  --abstr_ref_sig_restrict                funpre
% 2.14/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/0.98  --abstr_ref_under                       []
% 2.14/0.98  
% 2.14/0.98  ------ SAT Options
% 2.14/0.98  
% 2.14/0.98  --sat_mode                              false
% 2.14/0.98  --sat_fm_restart_options                ""
% 2.14/0.98  --sat_gr_def                            false
% 2.14/0.98  --sat_epr_types                         true
% 2.14/0.98  --sat_non_cyclic_types                  false
% 2.14/0.98  --sat_finite_models                     false
% 2.14/0.98  --sat_fm_lemmas                         false
% 2.14/0.98  --sat_fm_prep                           false
% 2.14/0.98  --sat_fm_uc_incr                        true
% 2.14/0.98  --sat_out_model                         small
% 2.14/0.98  --sat_out_clauses                       false
% 2.14/0.98  
% 2.14/0.98  ------ QBF Options
% 2.14/0.98  
% 2.14/0.98  --qbf_mode                              false
% 2.14/0.98  --qbf_elim_univ                         false
% 2.14/0.98  --qbf_dom_inst                          none
% 2.14/0.98  --qbf_dom_pre_inst                      false
% 2.14/0.98  --qbf_sk_in                             false
% 2.14/0.98  --qbf_pred_elim                         true
% 2.14/0.98  --qbf_split                             512
% 2.14/0.98  
% 2.14/0.98  ------ BMC1 Options
% 2.14/0.98  
% 2.14/0.98  --bmc1_incremental                      false
% 2.14/0.98  --bmc1_axioms                           reachable_all
% 2.14/0.98  --bmc1_min_bound                        0
% 2.14/0.98  --bmc1_max_bound                        -1
% 2.14/0.98  --bmc1_max_bound_default                -1
% 2.14/0.98  --bmc1_symbol_reachability              true
% 2.14/0.98  --bmc1_property_lemmas                  false
% 2.14/0.98  --bmc1_k_induction                      false
% 2.14/0.98  --bmc1_non_equiv_states                 false
% 2.14/0.98  --bmc1_deadlock                         false
% 2.14/0.98  --bmc1_ucm                              false
% 2.14/0.98  --bmc1_add_unsat_core                   none
% 2.14/0.98  --bmc1_unsat_core_children              false
% 2.14/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/0.98  --bmc1_out_stat                         full
% 2.14/0.98  --bmc1_ground_init                      false
% 2.14/0.98  --bmc1_pre_inst_next_state              false
% 2.14/0.98  --bmc1_pre_inst_state                   false
% 2.14/0.98  --bmc1_pre_inst_reach_state             false
% 2.14/0.98  --bmc1_out_unsat_core                   false
% 2.14/0.98  --bmc1_aig_witness_out                  false
% 2.14/0.98  --bmc1_verbose                          false
% 2.14/0.98  --bmc1_dump_clauses_tptp                false
% 2.14/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.14/0.98  --bmc1_dump_file                        -
% 2.14/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.14/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.14/0.98  --bmc1_ucm_extend_mode                  1
% 2.14/0.98  --bmc1_ucm_init_mode                    2
% 2.14/0.98  --bmc1_ucm_cone_mode                    none
% 2.14/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.14/0.98  --bmc1_ucm_relax_model                  4
% 2.14/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.14/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/0.98  --bmc1_ucm_layered_model                none
% 2.14/0.98  --bmc1_ucm_max_lemma_size               10
% 2.14/0.98  
% 2.14/0.98  ------ AIG Options
% 2.14/0.98  
% 2.14/0.98  --aig_mode                              false
% 2.14/0.98  
% 2.14/0.98  ------ Instantiation Options
% 2.14/0.98  
% 2.14/0.98  --instantiation_flag                    true
% 2.14/0.98  --inst_sos_flag                         false
% 2.14/0.98  --inst_sos_phase                        true
% 2.14/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/0.98  --inst_lit_sel_side                     num_symb
% 2.14/0.98  --inst_solver_per_active                1400
% 2.14/0.98  --inst_solver_calls_frac                1.
% 2.14/0.98  --inst_passive_queue_type               priority_queues
% 2.14/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/0.98  --inst_passive_queues_freq              [25;2]
% 2.14/0.98  --inst_dismatching                      true
% 2.14/0.98  --inst_eager_unprocessed_to_passive     true
% 2.14/0.98  --inst_prop_sim_given                   true
% 2.14/0.98  --inst_prop_sim_new                     false
% 2.14/0.98  --inst_subs_new                         false
% 2.14/0.98  --inst_eq_res_simp                      false
% 2.14/0.98  --inst_subs_given                       false
% 2.14/0.98  --inst_orphan_elimination               true
% 2.14/0.98  --inst_learning_loop_flag               true
% 2.14/0.98  --inst_learning_start                   3000
% 2.14/0.98  --inst_learning_factor                  2
% 2.14/0.98  --inst_start_prop_sim_after_learn       3
% 2.14/0.98  --inst_sel_renew                        solver
% 2.14/0.98  --inst_lit_activity_flag                true
% 2.14/0.98  --inst_restr_to_given                   false
% 2.14/0.98  --inst_activity_threshold               500
% 2.14/0.98  --inst_out_proof                        true
% 2.14/0.98  
% 2.14/0.98  ------ Resolution Options
% 2.14/0.98  
% 2.14/0.98  --resolution_flag                       true
% 2.14/0.98  --res_lit_sel                           adaptive
% 2.14/0.98  --res_lit_sel_side                      none
% 2.14/0.98  --res_ordering                          kbo
% 2.14/0.98  --res_to_prop_solver                    active
% 2.14/0.98  --res_prop_simpl_new                    false
% 2.14/0.98  --res_prop_simpl_given                  true
% 2.14/0.98  --res_passive_queue_type                priority_queues
% 2.14/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/0.98  --res_passive_queues_freq               [15;5]
% 2.14/0.98  --res_forward_subs                      full
% 2.14/0.98  --res_backward_subs                     full
% 2.14/0.98  --res_forward_subs_resolution           true
% 2.14/0.98  --res_backward_subs_resolution          true
% 2.14/0.98  --res_orphan_elimination                true
% 2.14/0.98  --res_time_limit                        2.
% 2.14/0.98  --res_out_proof                         true
% 2.14/0.98  
% 2.14/0.98  ------ Superposition Options
% 2.14/0.98  
% 2.14/0.98  --superposition_flag                    true
% 2.14/0.98  --sup_passive_queue_type                priority_queues
% 2.14/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.14/0.98  --demod_completeness_check              fast
% 2.14/0.98  --demod_use_ground                      true
% 2.14/0.98  --sup_to_prop_solver                    passive
% 2.14/0.98  --sup_prop_simpl_new                    true
% 2.14/0.98  --sup_prop_simpl_given                  true
% 2.14/0.98  --sup_fun_splitting                     false
% 2.14/0.98  --sup_smt_interval                      50000
% 2.14/0.98  
% 2.14/0.98  ------ Superposition Simplification Setup
% 2.14/0.98  
% 2.14/0.98  --sup_indices_passive                   []
% 2.14/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.98  --sup_full_bw                           [BwDemod]
% 2.14/0.98  --sup_immed_triv                        [TrivRules]
% 2.14/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.98  --sup_immed_bw_main                     []
% 2.14/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.98  
% 2.14/0.98  ------ Combination Options
% 2.14/0.98  
% 2.14/0.98  --comb_res_mult                         3
% 2.14/0.98  --comb_sup_mult                         2
% 2.14/0.98  --comb_inst_mult                        10
% 2.14/0.98  
% 2.14/0.98  ------ Debug Options
% 2.14/0.98  
% 2.14/0.98  --dbg_backtrace                         false
% 2.14/0.98  --dbg_dump_prop_clauses                 false
% 2.14/0.98  --dbg_dump_prop_clauses_file            -
% 2.14/0.98  --dbg_out_stat                          false
% 2.14/0.98  ------ Parsing...
% 2.14/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.14/0.98  
% 2.14/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.14/0.98  
% 2.14/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.14/0.98  
% 2.14/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.14/0.98  ------ Proving...
% 2.14/0.98  ------ Problem Properties 
% 2.14/0.98  
% 2.14/0.98  
% 2.14/0.98  clauses                                 31
% 2.14/0.98  conjectures                             17
% 2.14/0.98  EPR                                     16
% 2.14/0.98  Horn                                    22
% 2.14/0.98  unary                                   15
% 2.14/0.98  binary                                  2
% 2.14/0.98  lits                                    118
% 2.14/0.98  lits eq                                 5
% 2.14/0.98  fd_pure                                 0
% 2.14/0.98  fd_pseudo                               0
% 2.14/0.98  fd_cond                                 0
% 2.14/0.98  fd_pseudo_cond                          0
% 2.14/0.98  AC symbols                              0
% 2.14/0.98  
% 2.14/0.98  ------ Schedule dynamic 5 is on 
% 2.14/0.98  
% 2.14/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.14/0.98  
% 2.14/0.98  
% 2.14/0.98  ------ 
% 2.14/0.98  Current options:
% 2.14/0.98  ------ 
% 2.14/0.98  
% 2.14/0.98  ------ Input Options
% 2.14/0.98  
% 2.14/0.98  --out_options                           all
% 2.14/0.98  --tptp_safe_out                         true
% 2.14/0.98  --problem_path                          ""
% 2.14/0.98  --include_path                          ""
% 2.14/0.98  --clausifier                            res/vclausify_rel
% 2.14/0.98  --clausifier_options                    --mode clausify
% 2.14/0.98  --stdin                                 false
% 2.14/0.98  --stats_out                             all
% 2.14/0.98  
% 2.14/0.98  ------ General Options
% 2.14/0.98  
% 2.14/0.98  --fof                                   false
% 2.14/0.98  --time_out_real                         305.
% 2.14/0.98  --time_out_virtual                      -1.
% 2.14/0.98  --symbol_type_check                     false
% 2.14/0.98  --clausify_out                          false
% 2.14/0.98  --sig_cnt_out                           false
% 2.14/0.98  --trig_cnt_out                          false
% 2.14/0.98  --trig_cnt_out_tolerance                1.
% 2.14/0.98  --trig_cnt_out_sk_spl                   false
% 2.14/0.98  --abstr_cl_out                          false
% 2.14/0.98  
% 2.14/0.98  ------ Global Options
% 2.14/0.98  
% 2.14/0.98  --schedule                              default
% 2.14/0.98  --add_important_lit                     false
% 2.14/0.98  --prop_solver_per_cl                    1000
% 2.14/0.98  --min_unsat_core                        false
% 2.14/0.98  --soft_assumptions                      false
% 2.14/0.98  --soft_lemma_size                       3
% 2.14/0.98  --prop_impl_unit_size                   0
% 2.14/0.98  --prop_impl_unit                        []
% 2.14/0.98  --share_sel_clauses                     true
% 2.14/0.98  --reset_solvers                         false
% 2.14/0.98  --bc_imp_inh                            [conj_cone]
% 2.14/0.98  --conj_cone_tolerance                   3.
% 2.14/0.98  --extra_neg_conj                        none
% 2.14/0.98  --large_theory_mode                     true
% 2.14/0.98  --prolific_symb_bound                   200
% 2.14/0.98  --lt_threshold                          2000
% 2.14/0.98  --clause_weak_htbl                      true
% 2.14/0.98  --gc_record_bc_elim                     false
% 2.14/0.98  
% 2.14/0.98  ------ Preprocessing Options
% 2.14/0.98  
% 2.14/0.98  --preprocessing_flag                    true
% 2.14/0.98  --time_out_prep_mult                    0.1
% 2.14/0.98  --splitting_mode                        input
% 2.14/0.98  --splitting_grd                         true
% 2.14/0.98  --splitting_cvd                         false
% 2.14/0.98  --splitting_cvd_svl                     false
% 2.14/0.98  --splitting_nvd                         32
% 2.14/0.98  --sub_typing                            true
% 2.14/0.98  --prep_gs_sim                           true
% 2.14/0.98  --prep_unflatten                        true
% 2.14/0.98  --prep_res_sim                          true
% 2.14/0.98  --prep_upred                            true
% 2.14/0.98  --prep_sem_filter                       exhaustive
% 2.14/0.98  --prep_sem_filter_out                   false
% 2.14/0.98  --pred_elim                             true
% 2.14/0.98  --res_sim_input                         true
% 2.14/0.98  --eq_ax_congr_red                       true
% 2.14/0.98  --pure_diseq_elim                       true
% 2.14/0.98  --brand_transform                       false
% 2.14/0.98  --non_eq_to_eq                          false
% 2.14/0.98  --prep_def_merge                        true
% 2.14/0.98  --prep_def_merge_prop_impl              false
% 2.14/0.98  --prep_def_merge_mbd                    true
% 2.14/0.98  --prep_def_merge_tr_red                 false
% 2.14/0.98  --prep_def_merge_tr_cl                  false
% 2.14/0.98  --smt_preprocessing                     true
% 2.14/0.98  --smt_ac_axioms                         fast
% 2.14/0.98  --preprocessed_out                      false
% 2.14/0.98  --preprocessed_stats                    false
% 2.14/0.98  
% 2.14/0.98  ------ Abstraction refinement Options
% 2.14/0.98  
% 2.14/0.98  --abstr_ref                             []
% 2.14/0.98  --abstr_ref_prep                        false
% 2.14/0.98  --abstr_ref_until_sat                   false
% 2.14/0.98  --abstr_ref_sig_restrict                funpre
% 2.14/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/0.98  --abstr_ref_under                       []
% 2.14/0.98  
% 2.14/0.98  ------ SAT Options
% 2.14/0.98  
% 2.14/0.98  --sat_mode                              false
% 2.14/0.98  --sat_fm_restart_options                ""
% 2.14/0.98  --sat_gr_def                            false
% 2.14/0.98  --sat_epr_types                         true
% 2.14/0.98  --sat_non_cyclic_types                  false
% 2.14/0.98  --sat_finite_models                     false
% 2.14/0.98  --sat_fm_lemmas                         false
% 2.14/0.98  --sat_fm_prep                           false
% 2.14/0.98  --sat_fm_uc_incr                        true
% 2.14/0.98  --sat_out_model                         small
% 2.14/0.98  --sat_out_clauses                       false
% 2.14/0.98  
% 2.14/0.98  ------ QBF Options
% 2.14/0.98  
% 2.14/0.98  --qbf_mode                              false
% 2.14/0.98  --qbf_elim_univ                         false
% 2.14/0.98  --qbf_dom_inst                          none
% 2.14/0.98  --qbf_dom_pre_inst                      false
% 2.14/0.98  --qbf_sk_in                             false
% 2.14/0.98  --qbf_pred_elim                         true
% 2.14/0.98  --qbf_split                             512
% 2.14/0.98  
% 2.14/0.98  ------ BMC1 Options
% 2.14/0.98  
% 2.14/0.98  --bmc1_incremental                      false
% 2.14/0.98  --bmc1_axioms                           reachable_all
% 2.14/0.98  --bmc1_min_bound                        0
% 2.14/0.98  --bmc1_max_bound                        -1
% 2.14/0.98  --bmc1_max_bound_default                -1
% 2.14/0.98  --bmc1_symbol_reachability              true
% 2.14/0.98  --bmc1_property_lemmas                  false
% 2.14/0.98  --bmc1_k_induction                      false
% 2.14/0.98  --bmc1_non_equiv_states                 false
% 2.14/0.98  --bmc1_deadlock                         false
% 2.14/0.98  --bmc1_ucm                              false
% 2.14/0.98  --bmc1_add_unsat_core                   none
% 2.14/0.98  --bmc1_unsat_core_children              false
% 2.14/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/0.98  --bmc1_out_stat                         full
% 2.14/0.98  --bmc1_ground_init                      false
% 2.14/0.98  --bmc1_pre_inst_next_state              false
% 2.14/0.98  --bmc1_pre_inst_state                   false
% 2.14/0.98  --bmc1_pre_inst_reach_state             false
% 2.14/0.98  --bmc1_out_unsat_core                   false
% 2.14/0.98  --bmc1_aig_witness_out                  false
% 2.14/0.98  --bmc1_verbose                          false
% 2.14/0.98  --bmc1_dump_clauses_tptp                false
% 2.14/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.14/0.98  --bmc1_dump_file                        -
% 2.14/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.14/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.14/0.98  --bmc1_ucm_extend_mode                  1
% 2.14/0.98  --bmc1_ucm_init_mode                    2
% 2.14/0.98  --bmc1_ucm_cone_mode                    none
% 2.14/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.14/0.98  --bmc1_ucm_relax_model                  4
% 2.14/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.14/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/0.98  --bmc1_ucm_layered_model                none
% 2.14/0.98  --bmc1_ucm_max_lemma_size               10
% 2.14/0.98  
% 2.14/0.98  ------ AIG Options
% 2.14/0.98  
% 2.14/0.98  --aig_mode                              false
% 2.14/0.98  
% 2.14/0.98  ------ Instantiation Options
% 2.14/0.98  
% 2.14/0.98  --instantiation_flag                    true
% 2.14/0.98  --inst_sos_flag                         false
% 2.14/0.98  --inst_sos_phase                        true
% 2.14/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/0.98  --inst_lit_sel_side                     none
% 2.14/0.98  --inst_solver_per_active                1400
% 2.14/0.98  --inst_solver_calls_frac                1.
% 2.14/0.98  --inst_passive_queue_type               priority_queues
% 2.14/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/0.98  --inst_passive_queues_freq              [25;2]
% 2.14/0.98  --inst_dismatching                      true
% 2.14/0.98  --inst_eager_unprocessed_to_passive     true
% 2.14/0.98  --inst_prop_sim_given                   true
% 2.14/0.98  --inst_prop_sim_new                     false
% 2.14/0.98  --inst_subs_new                         false
% 2.14/0.98  --inst_eq_res_simp                      false
% 2.14/0.98  --inst_subs_given                       false
% 2.14/0.98  --inst_orphan_elimination               true
% 2.14/0.98  --inst_learning_loop_flag               true
% 2.14/0.98  --inst_learning_start                   3000
% 2.14/0.98  --inst_learning_factor                  2
% 2.14/0.98  --inst_start_prop_sim_after_learn       3
% 2.14/0.98  --inst_sel_renew                        solver
% 2.14/0.98  --inst_lit_activity_flag                true
% 2.14/0.98  --inst_restr_to_given                   false
% 2.14/0.98  --inst_activity_threshold               500
% 2.14/0.98  --inst_out_proof                        true
% 2.14/0.98  
% 2.14/0.98  ------ Resolution Options
% 2.14/0.98  
% 2.14/0.98  --resolution_flag                       false
% 2.14/0.98  --res_lit_sel                           adaptive
% 2.14/0.98  --res_lit_sel_side                      none
% 2.14/0.98  --res_ordering                          kbo
% 2.14/0.98  --res_to_prop_solver                    active
% 2.14/0.98  --res_prop_simpl_new                    false
% 2.14/0.98  --res_prop_simpl_given                  true
% 2.14/0.98  --res_passive_queue_type                priority_queues
% 2.14/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/0.98  --res_passive_queues_freq               [15;5]
% 2.14/0.98  --res_forward_subs                      full
% 2.14/0.98  --res_backward_subs                     full
% 2.14/0.98  --res_forward_subs_resolution           true
% 2.14/0.98  --res_backward_subs_resolution          true
% 2.14/0.98  --res_orphan_elimination                true
% 2.14/0.98  --res_time_limit                        2.
% 2.14/0.98  --res_out_proof                         true
% 2.14/0.98  
% 2.14/0.98  ------ Superposition Options
% 2.14/0.98  
% 2.14/0.98  --superposition_flag                    true
% 2.14/0.98  --sup_passive_queue_type                priority_queues
% 2.14/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.14/0.98  --demod_completeness_check              fast
% 2.14/0.98  --demod_use_ground                      true
% 2.14/0.98  --sup_to_prop_solver                    passive
% 2.14/0.98  --sup_prop_simpl_new                    true
% 2.14/0.98  --sup_prop_simpl_given                  true
% 2.14/0.98  --sup_fun_splitting                     false
% 2.14/0.98  --sup_smt_interval                      50000
% 2.14/0.98  
% 2.14/0.98  ------ Superposition Simplification Setup
% 2.14/0.98  
% 2.14/0.98  --sup_indices_passive                   []
% 2.14/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.98  --sup_full_bw                           [BwDemod]
% 2.14/0.98  --sup_immed_triv                        [TrivRules]
% 2.14/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.98  --sup_immed_bw_main                     []
% 2.14/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.98  
% 2.14/0.98  ------ Combination Options
% 2.14/0.98  
% 2.14/0.98  --comb_res_mult                         3
% 2.14/0.98  --comb_sup_mult                         2
% 2.14/0.98  --comb_inst_mult                        10
% 2.14/0.98  
% 2.14/0.98  ------ Debug Options
% 2.14/0.98  
% 2.14/0.98  --dbg_backtrace                         false
% 2.14/0.98  --dbg_dump_prop_clauses                 false
% 2.14/0.98  --dbg_dump_prop_clauses_file            -
% 2.14/0.98  --dbg_out_stat                          false
% 2.14/0.98  
% 2.14/0.98  
% 2.14/0.98  
% 2.14/0.98  
% 2.14/0.98  ------ Proving...
% 2.14/0.98  
% 2.14/0.98  
% 2.14/0.98  % SZS status Theorem for theBenchmark.p
% 2.14/0.98  
% 2.14/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.14/0.98  
% 2.14/0.98  fof(f11,axiom,(
% 2.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f31,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.98    inference(ennf_transformation,[],[f11])).
% 2.14/0.98  
% 2.14/0.98  fof(f32,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.98    inference(flattening,[],[f31])).
% 2.14/0.98  
% 2.14/0.98  fof(f42,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.98    inference(nnf_transformation,[],[f32])).
% 2.14/0.98  
% 2.14/0.98  fof(f70,plain,(
% 2.14/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f42])).
% 2.14/0.98  
% 2.14/0.98  fof(f97,plain,(
% 2.14/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(equality_resolution,[],[f70])).
% 2.14/0.98  
% 2.14/0.98  fof(f10,axiom,(
% 2.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f29,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.98    inference(ennf_transformation,[],[f10])).
% 2.14/0.98  
% 2.14/0.98  fof(f30,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.98    inference(flattening,[],[f29])).
% 2.14/0.98  
% 2.14/0.98  fof(f69,plain,(
% 2.14/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f30])).
% 2.14/0.98  
% 2.14/0.98  fof(f95,plain,(
% 2.14/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(equality_resolution,[],[f69])).
% 2.14/0.98  
% 2.14/0.98  fof(f12,conjecture,(
% 2.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f13,negated_conjecture,(
% 2.14/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 2.14/0.98    inference(negated_conjecture,[],[f12])).
% 2.14/0.98  
% 2.14/0.98  fof(f33,plain,(
% 2.14/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.14/0.98    inference(ennf_transformation,[],[f13])).
% 2.14/0.98  
% 2.14/0.98  fof(f34,plain,(
% 2.14/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X1,X4,X5) <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/0.98    inference(flattening,[],[f33])).
% 2.14/0.98  
% 2.14/0.98  fof(f43,plain,(
% 2.14/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/0.98    inference(nnf_transformation,[],[f34])).
% 2.14/0.98  
% 2.14/0.98  fof(f44,plain,(
% 2.14/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/0.98    inference(flattening,[],[f43])).
% 2.14/0.98  
% 2.14/0.98  fof(f51,plain,(
% 2.14/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) | r1_tmap_1(X3,X1,X4,X5)) & sK8 = X5 & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f50,plain,(
% 2.14/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,sK7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,sK7)) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f49,plain,(
% 2.14/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X6) | ~r1_tmap_1(X3,X1,sK6,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X6) | r1_tmap_1(X3,X1,sK6,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f48,plain,(
% 2.14/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X6) | ~r1_tmap_1(sK5,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X6) | r1_tmap_1(sK5,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(X2,sK5) & v1_tsep_1(X2,sK5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f47,plain,(
% 2.14/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK4,X3) & v1_tsep_1(sK4,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f46,plain,(
% 2.14/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK3,X4,X5)) & (r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X6) | r1_tmap_1(X3,sK3,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f45,plain,(
% 2.14/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5)) & (r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f52,plain,(
% 2.14/0.98    (((((((~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK3,sK6,sK7)) & (r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK3,sK6,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & v1_tsep_1(sK4,sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.14/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f44,f51,f50,f49,f48,f47,f46,f45])).
% 2.14/0.98  
% 2.14/0.98  fof(f83,plain,(
% 2.14/0.98    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f82,plain,(
% 2.14/0.98    v1_funct_1(sK6)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f9,axiom,(
% 2.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f27,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/0.98    inference(ennf_transformation,[],[f9])).
% 2.14/0.98  
% 2.14/0.98  fof(f28,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/0.98    inference(flattening,[],[f27])).
% 2.14/0.98  
% 2.14/0.98  fof(f68,plain,(
% 2.14/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f28])).
% 2.14/0.98  
% 2.14/0.98  fof(f6,axiom,(
% 2.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f22,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.98    inference(ennf_transformation,[],[f6])).
% 2.14/0.98  
% 2.14/0.98  fof(f23,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.98    inference(flattening,[],[f22])).
% 2.14/0.98  
% 2.14/0.98  fof(f35,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.98    inference(nnf_transformation,[],[f23])).
% 2.14/0.98  
% 2.14/0.98  fof(f36,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.98    inference(rectify,[],[f35])).
% 2.14/0.98  
% 2.14/0.98  fof(f38,plain,(
% 2.14/0.98    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f37,plain,(
% 2.14/0.98    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0))))),
% 2.14/0.98    introduced(choice_axiom,[])).
% 2.14/0.98  
% 2.14/0.98  fof(f39,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK0(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK1(X0,X1,X4),X1) & m1_connsp_2(sK1(X0,X1,X4),X0,X4) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 2.14/0.98  
% 2.14/0.98  fof(f60,plain,(
% 2.14/0.98    ( ! [X4,X0,X1] : (r1_tarski(sK1(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f39])).
% 2.14/0.98  
% 2.14/0.98  fof(f90,plain,(
% 2.14/0.98    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK3,sK6,sK7)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f89,plain,(
% 2.14/0.98    sK7 = sK8),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f59,plain,(
% 2.14/0.98    ( ! [X4,X0,X1] : (m1_connsp_2(sK1(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f39])).
% 2.14/0.98  
% 2.14/0.98  fof(f71,plain,(
% 2.14/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f42])).
% 2.14/0.98  
% 2.14/0.98  fof(f96,plain,(
% 2.14/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(equality_resolution,[],[f71])).
% 2.14/0.98  
% 2.14/0.98  fof(f2,axiom,(
% 2.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f16,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/0.98    inference(ennf_transformation,[],[f2])).
% 2.14/0.98  
% 2.14/0.98  fof(f17,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/0.98    inference(flattening,[],[f16])).
% 2.14/0.98  
% 2.14/0.98  fof(f54,plain,(
% 2.14/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f17])).
% 2.14/0.98  
% 2.14/0.98  fof(f4,axiom,(
% 2.14/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f19,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.14/0.98    inference(ennf_transformation,[],[f4])).
% 2.14/0.98  
% 2.14/0.98  fof(f56,plain,(
% 2.14/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f19])).
% 2.14/0.98  
% 2.14/0.98  fof(f58,plain,(
% 2.14/0.98    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f39])).
% 2.14/0.98  
% 2.14/0.98  fof(f75,plain,(
% 2.14/0.98    ~v2_struct_0(sK3)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f76,plain,(
% 2.14/0.98    v2_pre_topc(sK3)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f77,plain,(
% 2.14/0.98    l1_pre_topc(sK3)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f80,plain,(
% 2.14/0.98    ~v2_struct_0(sK5)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f84,plain,(
% 2.14/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f72,plain,(
% 2.14/0.98    ~v2_struct_0(sK2)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f73,plain,(
% 2.14/0.98    v2_pre_topc(sK2)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f74,plain,(
% 2.14/0.98    l1_pre_topc(sK2)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f78,plain,(
% 2.14/0.98    ~v2_struct_0(sK4)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f81,plain,(
% 2.14/0.98    m1_pre_topc(sK5,sK2)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f86,plain,(
% 2.14/0.98    m1_pre_topc(sK4,sK5)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f88,plain,(
% 2.14/0.98    m1_subset_1(sK8,u1_struct_0(sK4))),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f87,plain,(
% 2.14/0.98    m1_subset_1(sK7,u1_struct_0(sK5))),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f7,axiom,(
% 2.14/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f24,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/0.98    inference(ennf_transformation,[],[f7])).
% 2.14/0.98  
% 2.14/0.98  fof(f25,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/0.98    inference(flattening,[],[f24])).
% 2.14/0.98  
% 2.14/0.98  fof(f40,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/0.98    inference(nnf_transformation,[],[f25])).
% 2.14/0.98  
% 2.14/0.98  fof(f41,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/0.98    inference(flattening,[],[f40])).
% 2.14/0.98  
% 2.14/0.98  fof(f64,plain,(
% 2.14/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f41])).
% 2.14/0.98  
% 2.14/0.98  fof(f94,plain,(
% 2.14/0.98    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/0.98    inference(equality_resolution,[],[f64])).
% 2.14/0.98  
% 2.14/0.98  fof(f8,axiom,(
% 2.14/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f26,plain,(
% 2.14/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.14/0.98    inference(ennf_transformation,[],[f8])).
% 2.14/0.98  
% 2.14/0.98  fof(f67,plain,(
% 2.14/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f26])).
% 2.14/0.98  
% 2.14/0.98  fof(f85,plain,(
% 2.14/0.98    v1_tsep_1(sK4,sK5)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  fof(f1,axiom,(
% 2.14/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f14,plain,(
% 2.14/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.14/0.98    inference(ennf_transformation,[],[f1])).
% 2.14/0.98  
% 2.14/0.98  fof(f15,plain,(
% 2.14/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.14/0.98    inference(flattening,[],[f14])).
% 2.14/0.98  
% 2.14/0.98  fof(f53,plain,(
% 2.14/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f15])).
% 2.14/0.98  
% 2.14/0.98  fof(f3,axiom,(
% 2.14/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f18,plain,(
% 2.14/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.14/0.98    inference(ennf_transformation,[],[f3])).
% 2.14/0.98  
% 2.14/0.98  fof(f55,plain,(
% 2.14/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f18])).
% 2.14/0.98  
% 2.14/0.98  fof(f5,axiom,(
% 2.14/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.14/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.98  
% 2.14/0.98  fof(f20,plain,(
% 2.14/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.14/0.98    inference(ennf_transformation,[],[f5])).
% 2.14/0.98  
% 2.14/0.98  fof(f21,plain,(
% 2.14/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.14/0.98    inference(flattening,[],[f20])).
% 2.14/0.98  
% 2.14/0.98  fof(f57,plain,(
% 2.14/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.14/0.98    inference(cnf_transformation,[],[f21])).
% 2.14/0.98  
% 2.14/0.98  fof(f91,plain,(
% 2.14/0.98    ~r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK3,sK6,sK7)),
% 2.14/0.98    inference(cnf_transformation,[],[f52])).
% 2.14/0.98  
% 2.14/0.98  cnf(c_18,plain,
% 2.14/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/0.98      | ~ m1_connsp_2(X6,X0,X3)
% 2.14/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.14/0.98      | ~ m1_pre_topc(X0,X5)
% 2.14/0.98      | ~ m1_pre_topc(X4,X5)
% 2.14/0.98      | ~ m1_pre_topc(X4,X0)
% 2.14/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.98      | ~ v1_funct_1(X2)
% 2.14/0.98      | v2_struct_0(X5)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X4)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | ~ l1_pre_topc(X5)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X5)
% 2.14/0.98      | ~ v2_pre_topc(X1) ),
% 2.14/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_16,plain,
% 2.14/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/0.98      | ~ m1_pre_topc(X4,X5)
% 2.14/0.98      | ~ m1_pre_topc(X4,X0)
% 2.14/0.98      | ~ m1_pre_topc(X0,X5)
% 2.14/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.98      | ~ v1_funct_1(X2)
% 2.14/0.98      | v2_struct_0(X5)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | v2_struct_0(X4)
% 2.14/0.98      | ~ l1_pre_topc(X5)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X5)
% 2.14/0.98      | ~ v2_pre_topc(X1) ),
% 2.14/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_203,plain,
% 2.14/0.98      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_pre_topc(X4,X0)
% 2.14/0.98      | ~ m1_pre_topc(X4,X5)
% 2.14/0.98      | ~ m1_pre_topc(X0,X5)
% 2.14/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.98      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.98      | ~ v1_funct_1(X2)
% 2.14/0.98      | v2_struct_0(X5)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X4)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | ~ l1_pre_topc(X5)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X5)
% 2.14/0.98      | ~ v2_pre_topc(X1) ),
% 2.14/0.98      inference(global_propositional_subsumption,
% 2.14/0.98                [status(thm)],
% 2.14/0.98                [c_18,c_16]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_204,plain,
% 2.14/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/0.98      | ~ m1_pre_topc(X4,X0)
% 2.14/0.98      | ~ m1_pre_topc(X4,X5)
% 2.14/0.98      | ~ m1_pre_topc(X0,X5)
% 2.14/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.98      | ~ v1_funct_1(X2)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X4)
% 2.14/0.98      | v2_struct_0(X5)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ l1_pre_topc(X5)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X5) ),
% 2.14/0.98      inference(renaming,[status(thm)],[c_203]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_27,negated_conjecture,
% 2.14/0.98      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 2.14/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_938,plain,
% 2.14/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.98      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.98      | ~ m1_pre_topc(X4,X0)
% 2.14/0.98      | ~ m1_pre_topc(X4,X5)
% 2.14/0.98      | ~ m1_pre_topc(X0,X5)
% 2.14/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.98      | ~ v1_funct_1(X2)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X4)
% 2.14/0.98      | v2_struct_0(X5)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ l1_pre_topc(X5)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X5)
% 2.14/0.98      | u1_struct_0(X0) != u1_struct_0(sK5)
% 2.14/0.98      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.14/0.98      | sK6 != X2 ),
% 2.14/0.98      inference(resolution_lifted,[status(thm)],[c_204,c_27]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_939,plain,
% 2.14/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.14/0.98      | ~ r1_tmap_1(X3,X1,sK6,X4)
% 2.14/0.98      | ~ m1_pre_topc(X0,X3)
% 2.14/0.98      | ~ m1_pre_topc(X0,X2)
% 2.14/0.98      | ~ m1_pre_topc(X3,X2)
% 2.14/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/0.98      | ~ v1_funct_1(sK6)
% 2.14/0.98      | v2_struct_0(X3)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | v2_struct_0(X2)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ l1_pre_topc(X2)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X2)
% 2.14/0.98      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.14/0.98      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.14/0.98      inference(unflattening,[status(thm)],[c_938]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_28,negated_conjecture,
% 2.14/0.98      ( v1_funct_1(sK6) ),
% 2.14/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_943,plain,
% 2.14/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/0.98      | ~ m1_pre_topc(X3,X2)
% 2.14/0.98      | ~ m1_pre_topc(X0,X2)
% 2.14/0.98      | ~ m1_pre_topc(X0,X3)
% 2.14/0.98      | ~ r1_tmap_1(X3,X1,sK6,X4)
% 2.14/0.98      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.14/0.98      | v2_struct_0(X3)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | v2_struct_0(X2)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ l1_pre_topc(X2)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X2)
% 2.14/0.98      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.14/0.98      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.14/0.98      inference(global_propositional_subsumption,
% 2.14/0.98                [status(thm)],
% 2.14/0.98                [c_939,c_28]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_944,plain,
% 2.14/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.14/0.98      | ~ r1_tmap_1(X3,X1,sK6,X4)
% 2.14/0.98      | ~ m1_pre_topc(X0,X3)
% 2.14/0.98      | ~ m1_pre_topc(X3,X2)
% 2.14/0.98      | ~ m1_pre_topc(X0,X2)
% 2.14/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X2)
% 2.14/0.98      | v2_struct_0(X3)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ l1_pre_topc(X2)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X2)
% 2.14/0.98      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.14/0.98      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.14/0.98      inference(renaming,[status(thm)],[c_943]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_15,plain,
% 2.14/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.14/0.98      | ~ m1_pre_topc(X2,X0)
% 2.14/0.98      | m1_pre_topc(X2,X1)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X1) ),
% 2.14/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_985,plain,
% 2.14/0.98      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.14/0.98      | ~ r1_tmap_1(X3,X1,sK6,X4)
% 2.14/0.98      | ~ m1_pre_topc(X0,X3)
% 2.14/0.98      | ~ m1_pre_topc(X3,X2)
% 2.14/0.98      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/0.98      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X2)
% 2.14/0.98      | v2_struct_0(X3)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ l1_pre_topc(X2)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X2)
% 2.14/0.98      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.14/0.98      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.14/0.98      inference(forward_subsumption_resolution,
% 2.14/0.98                [status(thm)],
% 2.14/0.98                [c_944,c_15]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_2300,plain,
% 2.14/0.98      ( r1_tmap_1(X0_56,X1_56,k3_tmap_1(X2_56,X1_56,X3_56,X0_56,sK6),X0_57)
% 2.14/0.98      | ~ r1_tmap_1(X3_56,X1_56,sK6,X0_57)
% 2.14/0.98      | ~ m1_pre_topc(X0_56,X3_56)
% 2.14/0.98      | ~ m1_pre_topc(X3_56,X2_56)
% 2.14/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(X3_56))
% 2.14/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(X0_56))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X1_56))))
% 2.14/0.98      | v2_struct_0(X0_56)
% 2.14/0.98      | v2_struct_0(X1_56)
% 2.14/0.98      | v2_struct_0(X2_56)
% 2.14/0.98      | v2_struct_0(X3_56)
% 2.14/0.98      | ~ l1_pre_topc(X1_56)
% 2.14/0.98      | ~ l1_pre_topc(X2_56)
% 2.14/0.98      | ~ v2_pre_topc(X1_56)
% 2.14/0.98      | ~ v2_pre_topc(X2_56)
% 2.14/0.98      | u1_struct_0(X3_56) != u1_struct_0(sK5)
% 2.14/0.98      | u1_struct_0(X1_56) != u1_struct_0(sK3) ),
% 2.14/0.98      inference(subtyping,[status(esa)],[c_985]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_3406,plain,
% 2.14/0.98      ( r1_tmap_1(X0_56,X1_56,k3_tmap_1(X2_56,X1_56,sK5,X0_56,sK6),X0_57)
% 2.14/0.98      | ~ r1_tmap_1(sK5,X1_56,sK6,X0_57)
% 2.14/0.98      | ~ m1_pre_topc(X0_56,sK5)
% 2.14/0.98      | ~ m1_pre_topc(sK5,X2_56)
% 2.14/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(X0_56))
% 2.14/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK5))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_56))))
% 2.14/0.98      | v2_struct_0(X0_56)
% 2.14/0.98      | v2_struct_0(X1_56)
% 2.14/0.98      | v2_struct_0(X2_56)
% 2.14/0.98      | v2_struct_0(sK5)
% 2.14/0.98      | ~ l1_pre_topc(X1_56)
% 2.14/0.98      | ~ l1_pre_topc(X2_56)
% 2.14/0.98      | ~ v2_pre_topc(X1_56)
% 2.14/0.98      | ~ v2_pre_topc(X2_56)
% 2.14/0.98      | u1_struct_0(X1_56) != u1_struct_0(sK3)
% 2.14/0.98      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 2.14/0.98      inference(instantiation,[status(thm)],[c_2300]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_3793,plain,
% 2.14/0.98      ( ~ r1_tmap_1(sK5,X0_56,sK6,X0_57)
% 2.14/0.98      | r1_tmap_1(sK4,X0_56,k3_tmap_1(X1_56,X0_56,sK5,sK4,sK6),X0_57)
% 2.14/0.98      | ~ m1_pre_topc(sK5,X1_56)
% 2.14/0.98      | ~ m1_pre_topc(sK4,sK5)
% 2.14/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK5))
% 2.14/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK4))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
% 2.14/0.98      | v2_struct_0(X0_56)
% 2.14/0.98      | v2_struct_0(X1_56)
% 2.14/0.98      | v2_struct_0(sK5)
% 2.14/0.98      | v2_struct_0(sK4)
% 2.14/0.98      | ~ l1_pre_topc(X1_56)
% 2.14/0.98      | ~ l1_pre_topc(X0_56)
% 2.14/0.98      | ~ v2_pre_topc(X1_56)
% 2.14/0.98      | ~ v2_pre_topc(X0_56)
% 2.14/0.98      | u1_struct_0(X0_56) != u1_struct_0(sK3)
% 2.14/0.98      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 2.14/0.98      inference(instantiation,[status(thm)],[c_3406]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_3833,plain,
% 2.14/0.98      ( ~ r1_tmap_1(sK5,X0_56,sK6,X0_57)
% 2.14/0.98      | r1_tmap_1(sK4,X0_56,k3_tmap_1(sK2,X0_56,sK5,sK4,sK6),X0_57)
% 2.14/0.98      | ~ m1_pre_topc(sK5,sK2)
% 2.14/0.98      | ~ m1_pre_topc(sK4,sK5)
% 2.14/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK5))
% 2.14/0.98      | ~ m1_subset_1(X0_57,u1_struct_0(sK4))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
% 2.14/0.98      | v2_struct_0(X0_56)
% 2.14/0.98      | v2_struct_0(sK5)
% 2.14/0.98      | v2_struct_0(sK2)
% 2.14/0.98      | v2_struct_0(sK4)
% 2.14/0.98      | ~ l1_pre_topc(X0_56)
% 2.14/0.98      | ~ l1_pre_topc(sK2)
% 2.14/0.98      | ~ v2_pre_topc(X0_56)
% 2.14/0.98      | ~ v2_pre_topc(sK2)
% 2.14/0.98      | u1_struct_0(X0_56) != u1_struct_0(sK3)
% 2.14/0.98      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 2.14/0.98      inference(instantiation,[status(thm)],[c_3793]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_4741,plain,
% 2.14/0.98      ( ~ r1_tmap_1(sK5,X0_56,sK6,sK8)
% 2.14/0.98      | r1_tmap_1(sK4,X0_56,k3_tmap_1(sK2,X0_56,sK5,sK4,sK6),sK8)
% 2.14/0.98      | ~ m1_pre_topc(sK5,sK2)
% 2.14/0.98      | ~ m1_pre_topc(sK4,sK5)
% 2.14/0.98      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.14/0.98      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_56))))
% 2.14/0.98      | v2_struct_0(X0_56)
% 2.14/0.98      | v2_struct_0(sK5)
% 2.14/0.98      | v2_struct_0(sK2)
% 2.14/0.98      | v2_struct_0(sK4)
% 2.14/0.98      | ~ l1_pre_topc(X0_56)
% 2.14/0.98      | ~ l1_pre_topc(sK2)
% 2.14/0.98      | ~ v2_pre_topc(X0_56)
% 2.14/0.98      | ~ v2_pre_topc(sK2)
% 2.14/0.98      | u1_struct_0(X0_56) != u1_struct_0(sK3)
% 2.14/0.98      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 2.14/0.98      inference(instantiation,[status(thm)],[c_3833]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_4743,plain,
% 2.14/0.98      ( ~ r1_tmap_1(sK5,sK3,sK6,sK8)
% 2.14/0.98      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
% 2.14/0.98      | ~ m1_pre_topc(sK5,sK2)
% 2.14/0.98      | ~ m1_pre_topc(sK4,sK5)
% 2.14/0.98      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.14/0.98      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 2.14/0.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.14/0.98      | v2_struct_0(sK5)
% 2.14/0.98      | v2_struct_0(sK2)
% 2.14/0.98      | v2_struct_0(sK3)
% 2.14/0.98      | v2_struct_0(sK4)
% 2.14/0.98      | ~ l1_pre_topc(sK2)
% 2.14/0.98      | ~ l1_pre_topc(sK3)
% 2.14/0.98      | ~ v2_pre_topc(sK2)
% 2.14/0.98      | ~ v2_pre_topc(sK3)
% 2.14/0.98      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 2.14/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.14/0.98      inference(instantiation,[status(thm)],[c_4741]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_8,plain,
% 2.14/0.98      ( r1_tarski(sK1(X0,X1,X2),X1)
% 2.14/0.98      | ~ v3_pre_topc(X1,X0)
% 2.14/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.14/0.98      | ~ r2_hidden(X2,X1)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | ~ l1_pre_topc(X0)
% 2.14/0.98      | ~ v2_pre_topc(X0) ),
% 2.14/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_2325,plain,
% 2.14/0.98      ( r1_tarski(sK1(X0_56,X0_57,X1_57),X0_57)
% 2.14/0.98      | ~ v3_pre_topc(X0_57,X0_56)
% 2.14/0.98      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_56)))
% 2.14/0.98      | ~ m1_subset_1(X1_57,u1_struct_0(X0_56))
% 2.14/0.98      | ~ r2_hidden(X1_57,X0_57)
% 2.14/0.98      | v2_struct_0(X0_56)
% 2.14/0.98      | ~ l1_pre_topc(X0_56)
% 2.14/0.98      | ~ v2_pre_topc(X0_56) ),
% 2.14/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_3068,plain,
% 2.14/0.98      ( r1_tarski(sK1(X0_56,X0_57,X1_57),X0_57) = iProver_top
% 2.14/0.98      | v3_pre_topc(X0_57,X0_56) != iProver_top
% 2.14/0.98      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 2.14/0.98      | m1_subset_1(X1_57,u1_struct_0(X0_56)) != iProver_top
% 2.14/0.98      | r2_hidden(X1_57,X0_57) != iProver_top
% 2.14/0.98      | v2_struct_0(X0_56) = iProver_top
% 2.14/0.98      | l1_pre_topc(X0_56) != iProver_top
% 2.14/0.98      | v2_pre_topc(X0_56) != iProver_top ),
% 2.14/0.98      inference(predicate_to_equality,[status(thm)],[c_2325]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_20,negated_conjecture,
% 2.14/0.98      ( r1_tmap_1(sK5,sK3,sK6,sK7)
% 2.14/0.98      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
% 2.14/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_2320,negated_conjecture,
% 2.14/0.98      ( r1_tmap_1(sK5,sK3,sK6,sK7)
% 2.14/0.98      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
% 2.14/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_3073,plain,
% 2.14/0.98      ( r1_tmap_1(sK5,sK3,sK6,sK7) = iProver_top
% 2.14/0.98      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) = iProver_top ),
% 2.14/0.98      inference(predicate_to_equality,[status(thm)],[c_2320]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_21,negated_conjecture,
% 2.14/0.98      ( sK7 = sK8 ),
% 2.14/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_2319,negated_conjecture,
% 2.14/0.98      ( sK7 = sK8 ),
% 2.14/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_3148,plain,
% 2.14/0.98      ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
% 2.14/0.98      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) = iProver_top ),
% 2.14/0.98      inference(light_normalisation,[status(thm)],[c_3073,c_2319]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_9,plain,
% 2.14/0.98      ( m1_connsp_2(sK1(X0,X1,X2),X0,X2)
% 2.14/0.98      | ~ v3_pre_topc(X1,X0)
% 2.14/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.14/0.98      | ~ r2_hidden(X2,X1)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | ~ l1_pre_topc(X0)
% 2.14/0.98      | ~ v2_pre_topc(X0) ),
% 2.14/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_17,plain,
% 2.14/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/0.98      | ~ m1_connsp_2(X6,X0,X3)
% 2.14/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.14/0.98      | ~ m1_pre_topc(X0,X5)
% 2.14/0.98      | ~ m1_pre_topc(X4,X5)
% 2.14/0.98      | ~ m1_pre_topc(X4,X0)
% 2.14/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.98      | ~ v1_funct_1(X2)
% 2.14/0.98      | v2_struct_0(X5)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X4)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | ~ l1_pre_topc(X5)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X5)
% 2.14/0.98      | ~ v2_pre_topc(X1) ),
% 2.14/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_700,plain,
% 2.14/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/0.98      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.14/0.98      | ~ v3_pre_topc(X7,X8)
% 2.14/0.98      | ~ m1_pre_topc(X0,X5)
% 2.14/0.98      | ~ m1_pre_topc(X4,X5)
% 2.14/0.98      | ~ m1_pre_topc(X4,X0)
% 2.14/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
% 2.14/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.98      | ~ m1_subset_1(X9,u1_struct_0(X8))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.98      | ~ r2_hidden(X9,X7)
% 2.14/0.98      | ~ v1_funct_1(X2)
% 2.14/0.98      | v2_struct_0(X8)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | v2_struct_0(X5)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X4)
% 2.14/0.98      | ~ l1_pre_topc(X8)
% 2.14/0.98      | ~ l1_pre_topc(X5)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X8)
% 2.14/0.98      | ~ v2_pre_topc(X5)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | X0 != X8
% 2.14/0.98      | X3 != X9
% 2.14/0.98      | sK1(X8,X7,X9) != X6 ),
% 2.14/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_701,plain,
% 2.14/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.98      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/0.98      | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
% 2.14/0.98      | ~ v3_pre_topc(X6,X0)
% 2.14/0.98      | ~ m1_pre_topc(X4,X5)
% 2.14/0.98      | ~ m1_pre_topc(X0,X5)
% 2.14/0.98      | ~ m1_pre_topc(X4,X0)
% 2.14/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.98      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.98      | ~ m1_subset_1(sK1(X0,X6,X3),k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.98      | ~ r2_hidden(X3,X6)
% 2.14/0.98      | ~ v1_funct_1(X2)
% 2.14/0.98      | v2_struct_0(X1)
% 2.14/0.98      | v2_struct_0(X4)
% 2.14/0.98      | v2_struct_0(X5)
% 2.14/0.98      | v2_struct_0(X0)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ l1_pre_topc(X5)
% 2.14/0.98      | ~ l1_pre_topc(X0)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X5)
% 2.14/0.98      | ~ v2_pre_topc(X0) ),
% 2.14/0.98      inference(unflattening,[status(thm)],[c_700]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_1,plain,
% 2.14/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.14/0.98      | ~ l1_pre_topc(X1)
% 2.14/0.98      | ~ v2_pre_topc(X1)
% 2.14/0.98      | v2_pre_topc(X0) ),
% 2.14/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.14/0.98  
% 2.14/0.98  cnf(c_3,plain,
% 2.14/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.14/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_10,plain,
% 2.14/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.14/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.99      | ~ r2_hidden(X2,X0)
% 2.14/0.99      | v2_struct_0(X1)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X1) ),
% 2.14/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_755,plain,
% 2.14/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/0.99      | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
% 2.14/0.99      | ~ v3_pre_topc(X6,X0)
% 2.14/0.99      | ~ m1_pre_topc(X4,X0)
% 2.14/0.99      | ~ m1_pre_topc(X0,X5)
% 2.14/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.99      | ~ r2_hidden(X3,X6)
% 2.14/0.99      | ~ v1_funct_1(X2)
% 2.14/0.99      | v2_struct_0(X0)
% 2.14/0.99      | v2_struct_0(X1)
% 2.14/0.99      | v2_struct_0(X4)
% 2.14/0.99      | v2_struct_0(X5)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ l1_pre_topc(X5)
% 2.14/0.99      | ~ v2_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X5) ),
% 2.14/0.99      inference(forward_subsumption_resolution,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_701,c_1,c_3,c_10,c_15]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_884,plain,
% 2.14/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/0.99      | ~ r1_tarski(sK1(X0,X6,X3),u1_struct_0(X4))
% 2.14/0.99      | ~ v3_pre_topc(X6,X0)
% 2.14/0.99      | ~ m1_pre_topc(X4,X0)
% 2.14/0.99      | ~ m1_pre_topc(X0,X5)
% 2.14/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/0.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 2.14/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/0.99      | ~ r2_hidden(X3,X6)
% 2.14/0.99      | ~ v1_funct_1(X2)
% 2.14/0.99      | v2_struct_0(X0)
% 2.14/0.99      | v2_struct_0(X1)
% 2.14/0.99      | v2_struct_0(X4)
% 2.14/0.99      | v2_struct_0(X5)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ l1_pre_topc(X5)
% 2.14/0.99      | ~ v2_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X5)
% 2.14/0.99      | u1_struct_0(X0) != u1_struct_0(sK5)
% 2.14/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.14/0.99      | sK6 != X2 ),
% 2.14/0.99      inference(resolution_lifted,[status(thm)],[c_755,c_27]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_885,plain,
% 2.14/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.14/0.99      | r1_tmap_1(X3,X1,sK6,X4)
% 2.14/0.99      | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
% 2.14/0.99      | ~ v3_pre_topc(X5,X3)
% 2.14/0.99      | ~ m1_pre_topc(X0,X3)
% 2.14/0.99      | ~ m1_pre_topc(X3,X2)
% 2.14/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.14/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/0.99      | ~ r2_hidden(X4,X5)
% 2.14/0.99      | ~ v1_funct_1(sK6)
% 2.14/0.99      | v2_struct_0(X3)
% 2.14/0.99      | v2_struct_0(X1)
% 2.14/0.99      | v2_struct_0(X0)
% 2.14/0.99      | v2_struct_0(X2)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ l1_pre_topc(X2)
% 2.14/0.99      | ~ v2_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X2)
% 2.14/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.14/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.14/0.99      inference(unflattening,[status(thm)],[c_884]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_889,plain,
% 2.14/0.99      ( ~ r2_hidden(X4,X5)
% 2.14/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.14/0.99      | ~ m1_pre_topc(X3,X2)
% 2.14/0.99      | ~ m1_pre_topc(X0,X3)
% 2.14/0.99      | ~ v3_pre_topc(X5,X3)
% 2.14/0.99      | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
% 2.14/0.99      | r1_tmap_1(X3,X1,sK6,X4)
% 2.14/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.14/0.99      | v2_struct_0(X3)
% 2.14/0.99      | v2_struct_0(X1)
% 2.14/0.99      | v2_struct_0(X0)
% 2.14/0.99      | v2_struct_0(X2)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ l1_pre_topc(X2)
% 2.14/0.99      | ~ v2_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X2)
% 2.14/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.14/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.14/0.99      inference(global_propositional_subsumption,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_885,c_28]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_890,plain,
% 2.14/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK6),X4)
% 2.14/0.99      | r1_tmap_1(X3,X1,sK6,X4)
% 2.14/0.99      | ~ r1_tarski(sK1(X3,X5,X4),u1_struct_0(X0))
% 2.14/0.99      | ~ v3_pre_topc(X5,X3)
% 2.14/0.99      | ~ m1_pre_topc(X0,X3)
% 2.14/0.99      | ~ m1_pre_topc(X3,X2)
% 2.14/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 2.14/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/0.99      | ~ r2_hidden(X4,X5)
% 2.14/0.99      | v2_struct_0(X0)
% 2.14/0.99      | v2_struct_0(X1)
% 2.14/0.99      | v2_struct_0(X2)
% 2.14/0.99      | v2_struct_0(X3)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ l1_pre_topc(X2)
% 2.14/0.99      | ~ v2_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X2)
% 2.14/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 2.14/0.99      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.14/0.99      inference(renaming,[status(thm)],[c_889]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2301,plain,
% 2.14/0.99      ( ~ r1_tmap_1(X0_56,X1_56,k3_tmap_1(X2_56,X1_56,X3_56,X0_56,sK6),X0_57)
% 2.14/0.99      | r1_tmap_1(X3_56,X1_56,sK6,X0_57)
% 2.14/0.99      | ~ r1_tarski(sK1(X3_56,X1_57,X0_57),u1_struct_0(X0_56))
% 2.14/0.99      | ~ v3_pre_topc(X1_57,X3_56)
% 2.14/0.99      | ~ m1_pre_topc(X0_56,X3_56)
% 2.14/0.99      | ~ m1_pre_topc(X3_56,X2_56)
% 2.14/0.99      | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X3_56)))
% 2.14/0.99      | ~ m1_subset_1(X0_57,u1_struct_0(X3_56))
% 2.14/0.99      | ~ m1_subset_1(X0_57,u1_struct_0(X0_56))
% 2.14/0.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_56),u1_struct_0(X1_56))))
% 2.14/0.99      | ~ r2_hidden(X0_57,X1_57)
% 2.14/0.99      | v2_struct_0(X0_56)
% 2.14/0.99      | v2_struct_0(X1_56)
% 2.14/0.99      | v2_struct_0(X2_56)
% 2.14/0.99      | v2_struct_0(X3_56)
% 2.14/0.99      | ~ l1_pre_topc(X1_56)
% 2.14/0.99      | ~ l1_pre_topc(X2_56)
% 2.14/0.99      | ~ v2_pre_topc(X1_56)
% 2.14/0.99      | ~ v2_pre_topc(X2_56)
% 2.14/0.99      | u1_struct_0(X3_56) != u1_struct_0(sK5)
% 2.14/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK3) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_890]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3091,plain,
% 2.14/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK5)
% 2.14/0.99      | u1_struct_0(X1_56) != u1_struct_0(sK3)
% 2.14/0.99      | r1_tmap_1(X2_56,X1_56,k3_tmap_1(X3_56,X1_56,X0_56,X2_56,sK6),X0_57) != iProver_top
% 2.14/0.99      | r1_tmap_1(X0_56,X1_56,sK6,X0_57) = iProver_top
% 2.14/0.99      | r1_tarski(sK1(X0_56,X1_57,X0_57),u1_struct_0(X2_56)) != iProver_top
% 2.14/0.99      | v3_pre_topc(X1_57,X0_56) != iProver_top
% 2.14/0.99      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 2.14/0.99      | m1_pre_topc(X0_56,X3_56) != iProver_top
% 2.14/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X2_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 2.14/0.99      | r2_hidden(X0_57,X1_57) != iProver_top
% 2.14/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X3_56) = iProver_top
% 2.14/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.14/0.99      | l1_pre_topc(X3_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(X1_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(X3_56) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2301]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4525,plain,
% 2.14/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK5)
% 2.14/0.99      | r1_tmap_1(X1_56,sK3,k3_tmap_1(X2_56,sK3,X0_56,X1_56,sK6),X0_57) != iProver_top
% 2.14/0.99      | r1_tmap_1(X0_56,sK3,sK6,X0_57) = iProver_top
% 2.14/0.99      | r1_tarski(sK1(X0_56,X1_57,X0_57),u1_struct_0(X1_56)) != iProver_top
% 2.14/0.99      | v3_pre_topc(X1_57,X0_56) != iProver_top
% 2.14/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.14/0.99      | m1_pre_topc(X0_56,X2_56) != iProver_top
% 2.14/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X1_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
% 2.14/0.99      | r2_hidden(X0_57,X1_57) != iProver_top
% 2.14/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.14/0.99      | v2_struct_0(sK3) = iProver_top
% 2.14/0.99      | l1_pre_topc(X2_56) != iProver_top
% 2.14/0.99      | l1_pre_topc(sK3) != iProver_top
% 2.14/0.99      | v2_pre_topc(X2_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 2.14/0.99      inference(equality_resolution,[status(thm)],[c_3091]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_35,negated_conjecture,
% 2.14/0.99      ( ~ v2_struct_0(sK3) ),
% 2.14/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_42,plain,
% 2.14/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_34,negated_conjecture,
% 2.14/0.99      ( v2_pre_topc(sK3) ),
% 2.14/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_43,plain,
% 2.14/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_33,negated_conjecture,
% 2.14/0.99      ( l1_pre_topc(sK3) ),
% 2.14/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_44,plain,
% 2.14/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4594,plain,
% 2.14/0.99      ( v2_pre_topc(X2_56) != iProver_top
% 2.14/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.14/0.99      | r2_hidden(X0_57,X1_57) != iProver_top
% 2.14/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X1_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 2.14/0.99      | m1_pre_topc(X0_56,X2_56) != iProver_top
% 2.14/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.14/0.99      | v3_pre_topc(X1_57,X0_56) != iProver_top
% 2.14/0.99      | r1_tarski(sK1(X0_56,X1_57,X0_57),u1_struct_0(X1_56)) != iProver_top
% 2.14/0.99      | r1_tmap_1(X0_56,sK3,sK6,X0_57) = iProver_top
% 2.14/0.99      | r1_tmap_1(X1_56,sK3,k3_tmap_1(X2_56,sK3,X0_56,X1_56,sK6),X0_57) != iProver_top
% 2.14/0.99      | u1_struct_0(X0_56) != u1_struct_0(sK5)
% 2.14/0.99      | l1_pre_topc(X2_56) != iProver_top ),
% 2.14/0.99      inference(global_propositional_subsumption,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_4525,c_42,c_43,c_44]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4595,plain,
% 2.14/0.99      ( u1_struct_0(X0_56) != u1_struct_0(sK5)
% 2.14/0.99      | r1_tmap_1(X1_56,sK3,k3_tmap_1(X2_56,sK3,X0_56,X1_56,sK6),X0_57) != iProver_top
% 2.14/0.99      | r1_tmap_1(X0_56,sK3,sK6,X0_57) = iProver_top
% 2.14/0.99      | r1_tarski(sK1(X0_56,X1_57,X0_57),u1_struct_0(X1_56)) != iProver_top
% 2.14/0.99      | v3_pre_topc(X1_57,X0_56) != iProver_top
% 2.14/0.99      | m1_pre_topc(X1_56,X0_56) != iProver_top
% 2.14/0.99      | m1_pre_topc(X0_56,X2_56) != iProver_top
% 2.14/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(X0_56))) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X1_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(sK3)))) != iProver_top
% 2.14/0.99      | r2_hidden(X0_57,X1_57) != iProver_top
% 2.14/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X2_56) = iProver_top
% 2.14/0.99      | l1_pre_topc(X2_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(X2_56) != iProver_top ),
% 2.14/0.99      inference(renaming,[status(thm)],[c_4594]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4615,plain,
% 2.14/0.99      ( r1_tmap_1(X0_56,sK3,k3_tmap_1(X1_56,sK3,sK5,X0_56,sK6),X0_57) != iProver_top
% 2.14/0.99      | r1_tmap_1(sK5,sK3,sK6,X0_57) = iProver_top
% 2.14/0.99      | r1_tarski(sK1(sK5,X1_57,X0_57),u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | v3_pre_topc(X1_57,sK5) != iProver_top
% 2.14/0.99      | m1_pre_topc(X0_56,sK5) != iProver_top
% 2.14/0.99      | m1_pre_topc(sK5,X1_56) != iProver_top
% 2.14/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(sK5)) != iProver_top
% 2.14/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 2.14/0.99      | r2_hidden(X0_57,X1_57) != iProver_top
% 2.14/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.14/0.99      | v2_struct_0(sK5) = iProver_top
% 2.14/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(X1_56) != iProver_top ),
% 2.14/0.99      inference(equality_resolution,[status(thm)],[c_4595]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_30,negated_conjecture,
% 2.14/0.99      ( ~ v2_struct_0(sK5) ),
% 2.14/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_47,plain,
% 2.14/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_26,negated_conjecture,
% 2.14/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 2.14/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_51,plain,
% 2.14/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4675,plain,
% 2.14/0.99      ( v2_struct_0(X0_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.14/0.99      | r2_hidden(X0_57,X1_57) != iProver_top
% 2.14/0.99      | r1_tmap_1(X0_56,sK3,k3_tmap_1(X1_56,sK3,sK5,X0_56,sK6),X0_57) != iProver_top
% 2.14/0.99      | r1_tmap_1(sK5,sK3,sK6,X0_57) = iProver_top
% 2.14/0.99      | r1_tarski(sK1(sK5,X1_57,X0_57),u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | v3_pre_topc(X1_57,sK5) != iProver_top
% 2.14/0.99      | m1_pre_topc(X0_56,sK5) != iProver_top
% 2.14/0.99      | m1_pre_topc(sK5,X1_56) != iProver_top
% 2.14/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(sK5)) != iProver_top
% 2.14/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(X1_56) != iProver_top ),
% 2.14/0.99      inference(global_propositional_subsumption,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_4615,c_47,c_51]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4676,plain,
% 2.14/0.99      ( r1_tmap_1(X0_56,sK3,k3_tmap_1(X1_56,sK3,sK5,X0_56,sK6),X0_57) != iProver_top
% 2.14/0.99      | r1_tmap_1(sK5,sK3,sK6,X0_57) = iProver_top
% 2.14/0.99      | r1_tarski(sK1(sK5,X1_57,X0_57),u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | v3_pre_topc(X1_57,sK5) != iProver_top
% 2.14/0.99      | m1_pre_topc(X0_56,sK5) != iProver_top
% 2.14/0.99      | m1_pre_topc(sK5,X1_56) != iProver_top
% 2.14/0.99      | m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(X0_56)) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,u1_struct_0(sK5)) != iProver_top
% 2.14/0.99      | r2_hidden(X0_57,X1_57) != iProver_top
% 2.14/0.99      | v2_struct_0(X1_56) = iProver_top
% 2.14/0.99      | v2_struct_0(X0_56) = iProver_top
% 2.14/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(X1_56) != iProver_top ),
% 2.14/0.99      inference(renaming,[status(thm)],[c_4675]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4695,plain,
% 2.14/0.99      ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
% 2.14/0.99      | r1_tarski(sK1(sK5,X0_57,sK8),u1_struct_0(sK4)) != iProver_top
% 2.14/0.99      | v3_pre_topc(X0_57,sK5) != iProver_top
% 2.14/0.99      | m1_pre_topc(sK5,sK2) != iProver_top
% 2.14/0.99      | m1_pre_topc(sK4,sK5) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 2.14/0.99      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 2.14/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 2.14/0.99      | r2_hidden(sK8,X0_57) != iProver_top
% 2.14/0.99      | v2_struct_0(sK2) = iProver_top
% 2.14/0.99      | v2_struct_0(sK4) = iProver_top
% 2.14/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.14/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 2.14/0.99      inference(superposition,[status(thm)],[c_3148,c_4676]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_38,negated_conjecture,
% 2.14/0.99      ( ~ v2_struct_0(sK2) ),
% 2.14/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_39,plain,
% 2.14/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_37,negated_conjecture,
% 2.14/0.99      ( v2_pre_topc(sK2) ),
% 2.14/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_40,plain,
% 2.14/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_36,negated_conjecture,
% 2.14/0.99      ( l1_pre_topc(sK2) ),
% 2.14/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_41,plain,
% 2.14/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_32,negated_conjecture,
% 2.14/0.99      ( ~ v2_struct_0(sK4) ),
% 2.14/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_45,plain,
% 2.14/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_29,negated_conjecture,
% 2.14/0.99      ( m1_pre_topc(sK5,sK2) ),
% 2.14/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_48,plain,
% 2.14/0.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_24,negated_conjecture,
% 2.14/0.99      ( m1_pre_topc(sK4,sK5) ),
% 2.14/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_53,plain,
% 2.14/0.99      ( m1_pre_topc(sK4,sK5) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_22,negated_conjecture,
% 2.14/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 2.14/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_55,plain,
% 2.14/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_23,negated_conjecture,
% 2.14/0.99      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.14/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2317,negated_conjecture,
% 2.14/0.99      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3075,plain,
% 2.14/0.99      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2317]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3119,plain,
% 2.14/0.99      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 2.14/0.99      inference(light_normalisation,[status(thm)],[c_3075,c_2319]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4700,plain,
% 2.14/0.99      ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
% 2.14/0.99      | r1_tarski(sK1(sK5,X0_57,sK8),u1_struct_0(sK4)) != iProver_top
% 2.14/0.99      | v3_pre_topc(X0_57,sK5) != iProver_top
% 2.14/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 2.14/0.99      | r2_hidden(sK8,X0_57) != iProver_top ),
% 2.14/0.99      inference(global_propositional_subsumption,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_4695,c_39,c_40,c_41,c_45,c_48,c_53,c_55,c_3119]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4711,plain,
% 2.14/0.99      ( r1_tmap_1(sK5,sK3,sK6,sK8) = iProver_top
% 2.14/0.99      | v3_pre_topc(u1_struct_0(sK4),sK5) != iProver_top
% 2.14/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 2.14/0.99      | m1_subset_1(sK8,u1_struct_0(sK5)) != iProver_top
% 2.14/0.99      | r2_hidden(sK8,u1_struct_0(sK4)) != iProver_top
% 2.14/0.99      | v2_struct_0(sK5) = iProver_top
% 2.14/0.99      | l1_pre_topc(sK5) != iProver_top
% 2.14/0.99      | v2_pre_topc(sK5) != iProver_top ),
% 2.14/0.99      inference(superposition,[status(thm)],[c_3068,c_4700]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4712,plain,
% 2.14/0.99      ( r1_tmap_1(sK5,sK3,sK6,sK8)
% 2.14/0.99      | ~ v3_pre_topc(u1_struct_0(sK4),sK5)
% 2.14/0.99      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.14/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK5))
% 2.14/0.99      | ~ r2_hidden(sK8,u1_struct_0(sK4))
% 2.14/0.99      | v2_struct_0(sK5)
% 2.14/0.99      | ~ l1_pre_topc(sK5)
% 2.14/0.99      | ~ v2_pre_topc(sK5) ),
% 2.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4711]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2332,plain,( X0_57 = X0_57 ),theory(equality) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4380,plain,
% 2.14/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.14/0.99      inference(instantiation,[status(thm)],[c_2332]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2316,negated_conjecture,
% 2.14/0.99      ( m1_pre_topc(sK4,sK5) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3076,plain,
% 2.14/0.99      ( m1_pre_topc(sK4,sK5) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2316]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2328,plain,
% 2.14/0.99      ( ~ m1_pre_topc(X0_56,X1_56)
% 2.14/0.99      | ~ l1_pre_topc(X1_56)
% 2.14/0.99      | l1_pre_topc(X0_56) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3065,plain,
% 2.14/0.99      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 2.14/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.14/0.99      | l1_pre_topc(X0_56) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2328]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3879,plain,
% 2.14/0.99      ( l1_pre_topc(sK5) != iProver_top
% 2.14/0.99      | l1_pre_topc(sK4) = iProver_top ),
% 2.14/0.99      inference(superposition,[status(thm)],[c_3076,c_3065]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3894,plain,
% 2.14/0.99      ( ~ l1_pre_topc(sK5) | l1_pre_topc(sK4) ),
% 2.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3879]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2314,negated_conjecture,
% 2.14/0.99      ( m1_pre_topc(sK5,sK2) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_29]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3078,plain,
% 2.14/0.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2314]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2329,plain,
% 2.14/0.99      ( ~ m1_pre_topc(X0_56,X1_56)
% 2.14/0.99      | ~ l1_pre_topc(X1_56)
% 2.14/0.99      | ~ v2_pre_topc(X1_56)
% 2.14/0.99      | v2_pre_topc(X0_56) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3064,plain,
% 2.14/0.99      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 2.14/0.99      | l1_pre_topc(X1_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(X1_56) != iProver_top
% 2.14/0.99      | v2_pre_topc(X0_56) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2329]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3852,plain,
% 2.14/0.99      ( l1_pre_topc(sK2) != iProver_top
% 2.14/0.99      | v2_pre_topc(sK5) = iProver_top
% 2.14/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 2.14/0.99      inference(superposition,[status(thm)],[c_3078,c_3064]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3873,plain,
% 2.14/0.99      ( ~ l1_pre_topc(sK2) | v2_pre_topc(sK5) | ~ v2_pre_topc(sK2) ),
% 2.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3852]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_13,plain,
% 2.14/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.14/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.14/0.99      | ~ m1_pre_topc(X0,X1)
% 2.14/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X1) ),
% 2.14/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_14,plain,
% 2.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.14/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.99      | ~ l1_pre_topc(X1) ),
% 2.14/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_212,plain,
% 2.14/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.14/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.14/0.99      | ~ v1_tsep_1(X0,X1)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X1) ),
% 2.14/0.99      inference(global_propositional_subsumption,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_13,c_14]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_213,plain,
% 2.14/0.99      ( ~ v1_tsep_1(X0,X1)
% 2.14/0.99      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.14/0.99      | ~ m1_pre_topc(X0,X1)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X1) ),
% 2.14/0.99      inference(renaming,[status(thm)],[c_212]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_25,negated_conjecture,
% 2.14/0.99      ( v1_tsep_1(sK4,sK5) ),
% 2.14/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_536,plain,
% 2.14/0.99      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.14/0.99      | ~ m1_pre_topc(X0,X1)
% 2.14/0.99      | ~ l1_pre_topc(X1)
% 2.14/0.99      | ~ v2_pre_topc(X1)
% 2.14/0.99      | sK5 != X1
% 2.14/0.99      | sK4 != X0 ),
% 2.14/0.99      inference(resolution_lifted,[status(thm)],[c_213,c_25]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_537,plain,
% 2.14/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK5)
% 2.14/0.99      | ~ m1_pre_topc(sK4,sK5)
% 2.14/0.99      | ~ l1_pre_topc(sK5)
% 2.14/0.99      | ~ v2_pre_topc(sK5) ),
% 2.14/0.99      inference(unflattening,[status(thm)],[c_536]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_539,plain,
% 2.14/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK5)
% 2.14/0.99      | ~ l1_pre_topc(sK5)
% 2.14/0.99      | ~ v2_pre_topc(sK5) ),
% 2.14/0.99      inference(global_propositional_subsumption,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_537,c_24]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2303,plain,
% 2.14/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK5)
% 2.14/0.99      | ~ l1_pre_topc(sK5)
% 2.14/0.99      | ~ v2_pre_topc(sK5) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_539]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3089,plain,
% 2.14/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK5) = iProver_top
% 2.14/0.99      | l1_pre_topc(sK5) != iProver_top
% 2.14/0.99      | v2_pre_topc(sK5) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2303]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_538,plain,
% 2.14/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK5) = iProver_top
% 2.14/0.99      | m1_pre_topc(sK4,sK5) != iProver_top
% 2.14/0.99      | l1_pre_topc(sK5) != iProver_top
% 2.14/0.99      | v2_pre_topc(sK5) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3416,plain,
% 2.14/0.99      ( ~ m1_pre_topc(sK5,X0_56)
% 2.14/0.99      | ~ l1_pre_topc(X0_56)
% 2.14/0.99      | l1_pre_topc(sK5) ),
% 2.14/0.99      inference(instantiation,[status(thm)],[c_2328]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3725,plain,
% 2.14/0.99      ( ~ m1_pre_topc(sK5,sK2) | l1_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 2.14/0.99      inference(instantiation,[status(thm)],[c_3416]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3726,plain,
% 2.14/0.99      ( m1_pre_topc(sK5,sK2) != iProver_top
% 2.14/0.99      | l1_pre_topc(sK5) = iProver_top
% 2.14/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_3725]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3804,plain,
% 2.14/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK5) = iProver_top
% 2.14/0.99      | v2_pre_topc(sK5) != iProver_top ),
% 2.14/0.99      inference(global_propositional_subsumption,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_3089,c_41,c_48,c_53,c_538,c_3726]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3806,plain,
% 2.14/0.99      ( v3_pre_topc(u1_struct_0(sK4),sK5) | ~ v2_pre_topc(sK5) ),
% 2.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3804]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2318,negated_conjecture,
% 2.14/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3074,plain,
% 2.14/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2318]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_0,plain,
% 2.14/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.14/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2330,plain,
% 2.14/0.99      ( ~ m1_subset_1(X0_57,X1_57)
% 2.14/0.99      | r2_hidden(X0_57,X1_57)
% 2.14/0.99      | v1_xboole_0(X1_57) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3063,plain,
% 2.14/0.99      ( m1_subset_1(X0_57,X1_57) != iProver_top
% 2.14/0.99      | r2_hidden(X0_57,X1_57) = iProver_top
% 2.14/0.99      | v1_xboole_0(X1_57) = iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2330]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3715,plain,
% 2.14/0.99      ( r2_hidden(sK8,u1_struct_0(sK4)) = iProver_top
% 2.14/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.14/0.99      inference(superposition,[status(thm)],[c_3074,c_3063]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3716,plain,
% 2.14/0.99      ( r2_hidden(sK8,u1_struct_0(sK4)) | v1_xboole_0(u1_struct_0(sK4)) ),
% 2.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3715]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2,plain,
% 2.14/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.14/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_4,plain,
% 2.14/0.99      ( v2_struct_0(X0)
% 2.14/0.99      | ~ l1_struct_0(X0)
% 2.14/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.14/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_495,plain,
% 2.14/0.99      ( v2_struct_0(X0)
% 2.14/0.99      | ~ l1_pre_topc(X0)
% 2.14/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.14/0.99      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2304,plain,
% 2.14/0.99      ( v2_struct_0(X0_56)
% 2.14/0.99      | ~ l1_pre_topc(X0_56)
% 2.14/0.99      | ~ v1_xboole_0(u1_struct_0(X0_56)) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_495]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3526,plain,
% 2.14/0.99      ( v2_struct_0(sK4)
% 2.14/0.99      | ~ l1_pre_topc(sK4)
% 2.14/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.14/0.99      inference(instantiation,[status(thm)],[c_2304]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2323,plain,
% 2.14/0.99      ( ~ m1_pre_topc(X0_56,X1_56)
% 2.14/0.99      | m1_subset_1(u1_struct_0(X0_56),k1_zfmisc_1(u1_struct_0(X1_56)))
% 2.14/0.99      | ~ l1_pre_topc(X1_56) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3421,plain,
% 2.14/0.99      ( ~ m1_pre_topc(sK4,sK5)
% 2.14/0.99      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK5)))
% 2.14/0.99      | ~ l1_pre_topc(sK5) ),
% 2.14/0.99      inference(instantiation,[status(thm)],[c_2323]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3405,plain,
% 2.14/0.99      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 2.14/0.99      inference(instantiation,[status(thm)],[c_2332]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3347,plain,
% 2.14/0.99      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 2.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3119]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_19,negated_conjecture,
% 2.14/0.99      ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
% 2.14/0.99      | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
% 2.14/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_2321,negated_conjecture,
% 2.14/0.99      ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
% 2.14/0.99      | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
% 2.14/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3072,plain,
% 2.14/0.99      ( r1_tmap_1(sK5,sK3,sK6,sK7) != iProver_top
% 2.14/0.99      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) != iProver_top ),
% 2.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2321]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3159,plain,
% 2.14/0.99      ( r1_tmap_1(sK5,sK3,sK6,sK8) != iProver_top
% 2.14/0.99      | r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) != iProver_top ),
% 2.14/0.99      inference(light_normalisation,[status(thm)],[c_3072,c_2319]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(c_3333,plain,
% 2.14/0.99      ( ~ r1_tmap_1(sK5,sK3,sK6,sK8)
% 2.14/0.99      | ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
% 2.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3159]) ).
% 2.14/0.99  
% 2.14/0.99  cnf(contradiction,plain,
% 2.14/0.99      ( $false ),
% 2.14/0.99      inference(minisat,
% 2.14/0.99                [status(thm)],
% 2.14/0.99                [c_4743,c_4712,c_4380,c_3894,c_3873,c_3806,c_3725,c_3716,
% 2.14/0.99                 c_3526,c_3421,c_3405,c_3347,c_3333,c_22,c_24,c_26,c_29,
% 2.14/0.99                 c_30,c_32,c_33,c_34,c_35,c_36,c_37,c_38]) ).
% 2.14/0.99  
% 2.14/0.99  
% 2.14/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.14/0.99  
% 2.14/0.99  ------                               Statistics
% 2.14/0.99  
% 2.14/0.99  ------ General
% 2.14/0.99  
% 2.14/0.99  abstr_ref_over_cycles:                  0
% 2.14/0.99  abstr_ref_under_cycles:                 0
% 2.14/0.99  gc_basic_clause_elim:                   0
% 2.14/0.99  forced_gc_time:                         0
% 2.14/0.99  parsing_time:                           0.013
% 2.14/0.99  unif_index_cands_time:                  0.
% 2.14/0.99  unif_index_add_time:                    0.
% 2.14/0.99  orderings_time:                         0.
% 2.14/0.99  out_proof_time:                         0.016
% 2.14/0.99  total_time:                             0.186
% 2.14/0.99  num_of_symbols:                         61
% 2.14/0.99  num_of_terms:                           3731
% 2.14/0.99  
% 2.14/0.99  ------ Preprocessing
% 2.14/0.99  
% 2.14/0.99  num_of_splits:                          0
% 2.14/0.99  num_of_split_atoms:                     0
% 2.14/0.99  num_of_reused_defs:                     0
% 2.14/0.99  num_eq_ax_congr_red:                    32
% 2.14/0.99  num_of_sem_filtered_clauses:            1
% 2.14/0.99  num_of_subtypes:                        2
% 2.14/0.99  monotx_restored_types:                  0
% 2.14/0.99  sat_num_of_epr_types:                   0
% 2.14/0.99  sat_num_of_non_cyclic_types:            0
% 2.14/0.99  sat_guarded_non_collapsed_types:        0
% 2.14/0.99  num_pure_diseq_elim:                    0
% 2.14/0.99  simp_replaced_by:                       0
% 2.14/0.99  res_preprocessed:                       156
% 2.14/0.99  prep_upred:                             0
% 2.14/0.99  prep_unflattend:                        53
% 2.14/0.99  smt_new_axioms:                         0
% 2.14/0.99  pred_elim_cands:                        10
% 2.14/0.99  pred_elim:                              5
% 2.14/0.99  pred_elim_cl:                           7
% 2.14/0.99  pred_elim_cycles:                       13
% 2.14/0.99  merged_defs:                            8
% 2.14/0.99  merged_defs_ncl:                        0
% 2.14/0.99  bin_hyper_res:                          8
% 2.14/0.99  prep_cycles:                            4
% 2.14/0.99  pred_elim_time:                         0.05
% 2.14/0.99  splitting_time:                         0.
% 2.14/0.99  sem_filter_time:                        0.
% 2.14/0.99  monotx_time:                            0.
% 2.14/0.99  subtype_inf_time:                       0.
% 2.14/0.99  
% 2.14/0.99  ------ Problem properties
% 2.14/0.99  
% 2.14/0.99  clauses:                                31
% 2.14/0.99  conjectures:                            17
% 2.14/0.99  epr:                                    16
% 2.14/0.99  horn:                                   22
% 2.14/0.99  ground:                                 18
% 2.14/0.99  unary:                                  15
% 2.14/0.99  binary:                                 2
% 2.14/0.99  lits:                                   118
% 2.14/0.99  lits_eq:                                5
% 2.14/0.99  fd_pure:                                0
% 2.14/0.99  fd_pseudo:                              0
% 2.14/0.99  fd_cond:                                0
% 2.14/0.99  fd_pseudo_cond:                         0
% 2.14/0.99  ac_symbols:                             0
% 2.14/0.99  
% 2.14/0.99  ------ Propositional Solver
% 2.14/0.99  
% 2.14/0.99  prop_solver_calls:                      28
% 2.14/0.99  prop_fast_solver_calls:                 2031
% 2.14/0.99  smt_solver_calls:                       0
% 2.14/0.99  smt_fast_solver_calls:                  0
% 2.14/0.99  prop_num_of_clauses:                    841
% 2.14/0.99  prop_preprocess_simplified:             4379
% 2.14/0.99  prop_fo_subsumed:                       43
% 2.14/0.99  prop_solver_time:                       0.
% 2.14/0.99  smt_solver_time:                        0.
% 2.14/0.99  smt_fast_solver_time:                   0.
% 2.14/0.99  prop_fast_solver_time:                  0.
% 2.14/0.99  prop_unsat_core_time:                   0.
% 2.14/0.99  
% 2.14/0.99  ------ QBF
% 2.14/0.99  
% 2.14/0.99  qbf_q_res:                              0
% 2.14/0.99  qbf_num_tautologies:                    0
% 2.14/0.99  qbf_prep_cycles:                        0
% 2.14/0.99  
% 2.14/0.99  ------ BMC1
% 2.14/0.99  
% 2.14/0.99  bmc1_current_bound:                     -1
% 2.14/0.99  bmc1_last_solved_bound:                 -1
% 2.14/0.99  bmc1_unsat_core_size:                   -1
% 2.14/0.99  bmc1_unsat_core_parents_size:           -1
% 2.14/0.99  bmc1_merge_next_fun:                    0
% 2.14/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.14/0.99  
% 2.14/0.99  ------ Instantiation
% 2.14/0.99  
% 2.14/0.99  inst_num_of_clauses:                    233
% 2.14/0.99  inst_num_in_passive:                    26
% 2.14/0.99  inst_num_in_active:                     188
% 2.14/0.99  inst_num_in_unprocessed:                18
% 2.14/0.99  inst_num_of_loops:                      225
% 2.14/0.99  inst_num_of_learning_restarts:          0
% 2.14/0.99  inst_num_moves_active_passive:          32
% 2.14/0.99  inst_lit_activity:                      0
% 2.14/0.99  inst_lit_activity_moves:                0
% 2.14/0.99  inst_num_tautologies:                   0
% 2.14/0.99  inst_num_prop_implied:                  0
% 2.14/0.99  inst_num_existing_simplified:           0
% 2.14/0.99  inst_num_eq_res_simplified:             0
% 2.14/0.99  inst_num_child_elim:                    0
% 2.14/0.99  inst_num_of_dismatching_blockings:      8
% 2.14/0.99  inst_num_of_non_proper_insts:           209
% 2.14/0.99  inst_num_of_duplicates:                 0
% 2.14/0.99  inst_inst_num_from_inst_to_res:         0
% 2.14/0.99  inst_dismatching_checking_time:         0.
% 2.14/0.99  
% 2.14/0.99  ------ Resolution
% 2.14/0.99  
% 2.14/0.99  res_num_of_clauses:                     0
% 2.14/0.99  res_num_in_passive:                     0
% 2.14/0.99  res_num_in_active:                      0
% 2.14/0.99  res_num_of_loops:                       160
% 2.14/0.99  res_forward_subset_subsumed:            31
% 2.14/0.99  res_backward_subset_subsumed:           0
% 2.14/0.99  res_forward_subsumed:                   0
% 2.14/0.99  res_backward_subsumed:                  0
% 2.14/0.99  res_forward_subsumption_resolution:     8
% 2.14/0.99  res_backward_subsumption_resolution:    0
% 2.14/0.99  res_clause_to_clause_subsumption:       228
% 2.14/0.99  res_orphan_elimination:                 0
% 2.14/0.99  res_tautology_del:                      68
% 2.14/0.99  res_num_eq_res_simplified:              0
% 2.14/0.99  res_num_sel_changes:                    0
% 2.14/0.99  res_moves_from_active_to_pass:          0
% 2.14/0.99  
% 2.14/0.99  ------ Superposition
% 2.14/0.99  
% 2.14/0.99  sup_time_total:                         0.
% 2.14/0.99  sup_time_generating:                    0.
% 2.14/0.99  sup_time_sim_full:                      0.
% 2.14/0.99  sup_time_sim_immed:                     0.
% 2.14/0.99  
% 2.14/0.99  sup_num_of_clauses:                     53
% 2.14/0.99  sup_num_in_active:                      44
% 2.14/0.99  sup_num_in_passive:                     9
% 2.14/0.99  sup_num_of_loops:                       44
% 2.14/0.99  sup_fw_superposition:                   13
% 2.14/0.99  sup_bw_superposition:                   8
% 2.14/0.99  sup_immediate_simplified:               0
% 2.14/0.99  sup_given_eliminated:                   0
% 2.14/0.99  comparisons_done:                       0
% 2.14/0.99  comparisons_avoided:                    0
% 2.14/0.99  
% 2.14/0.99  ------ Simplifications
% 2.14/0.99  
% 2.14/0.99  
% 2.14/0.99  sim_fw_subset_subsumed:                 0
% 2.14/0.99  sim_bw_subset_subsumed:                 0
% 2.14/0.99  sim_fw_subsumed:                        0
% 2.14/0.99  sim_bw_subsumed:                        0
% 2.14/0.99  sim_fw_subsumption_res:                 0
% 2.14/0.99  sim_bw_subsumption_res:                 0
% 2.14/0.99  sim_tautology_del:                      1
% 2.14/0.99  sim_eq_tautology_del:                   0
% 2.14/0.99  sim_eq_res_simp:                        0
% 2.14/0.99  sim_fw_demodulated:                     0
% 2.14/0.99  sim_bw_demodulated:                     0
% 2.14/0.99  sim_light_normalised:                   3
% 2.14/0.99  sim_joinable_taut:                      0
% 2.14/0.99  sim_joinable_simp:                      0
% 2.14/0.99  sim_ac_normalised:                      0
% 2.14/0.99  sim_smt_subsumption:                    0
% 2.14/0.99  
%------------------------------------------------------------------------------
