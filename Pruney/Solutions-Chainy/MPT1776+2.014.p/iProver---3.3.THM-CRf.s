%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:23 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 647 expanded)
%              Number of clauses        :  120 ( 149 expanded)
%              Number of leaves         :   21 ( 253 expanded)
%              Depth                    :   21
%              Number of atoms          : 1541 (12086 expanded)
%              Number of equality atoms :  266 ( 895 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal clause size      :   46 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X5)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f53])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f52])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X0,X4,X5) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | r1_tmap_1(X3,X0,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | ~ r1_tmap_1(X3,X0,X4,X5) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7)
          | r1_tmap_1(X3,X0,X4,X5) )
        & sK7 = X5
        & m1_subset_1(sK7,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                | ~ r1_tmap_1(X3,X0,X4,X5) )
              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                | r1_tmap_1(X3,X0,X4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | ~ r1_tmap_1(X3,X0,X4,sK6) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | r1_tmap_1(X3,X0,X4,sK6) )
            & sK6 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                    | ~ r1_tmap_1(X3,X0,X4,X5) )
                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                    | r1_tmap_1(X3,X0,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_pre_topc(X2,X3)
          & m1_pre_topc(X2,X1)
          & v1_tsep_1(X2,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6)
                  | ~ r1_tmap_1(X3,X0,sK5,X5) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6)
                  | r1_tmap_1(X3,X0,sK5,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_pre_topc(X2,X1)
        & v1_tsep_1(X2,X1)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                        | ~ r1_tmap_1(X3,X0,X4,X5) )
                      & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                        | r1_tmap_1(X3,X0,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(X2,X1)
              & v1_tsep_1(X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6)
                      | ~ r1_tmap_1(sK4,X0,X4,X5) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6)
                      | r1_tmap_1(sK4,X0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_pre_topc(X2,sK4)
            & m1_pre_topc(X2,X1)
            & v1_tsep_1(X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,X0,X4,X5) )
                          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                            | r1_tmap_1(X3,X0,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,X1)
                  & v1_tsep_1(X2,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6)
                          | ~ r1_tmap_1(X3,X0,X4,X5) )
                        & ( r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6)
                          | r1_tmap_1(X3,X0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK3)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK3,X3)
                & m1_pre_topc(sK3,X1)
                & v1_tsep_1(sK3,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X0,X4,X5) )
                            & ( r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X0,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,sK2)
                    & v1_tsep_1(X2,sK2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X0,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X2,X1)
                        & v1_tsep_1(X2,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
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
                              ( ( ~ r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK1,X4,X5) )
                              & ( r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
      | ~ r1_tmap_1(sK4,sK1,sK5,sK6) )
    & ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
      | r1_tmap_1(sK4,sK1,sK5,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK3,sK2)
    & v1_tsep_1(sK3,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f39,f38,f37,f36,f35,f34,f33])).

fof(f66,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | r1_tmap_1(sK4,sK1,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,
    ( ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | ~ r1_tmap_1(sK4,sK1,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_11,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_178,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_11])).

cnf(c_179,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_705,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_23])).

cnf(c_706,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_710,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_706,c_24])).

cnf(c_711,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_710])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_752,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ r1_tmap_1(X3,X1,sK5,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_711,c_10])).

cnf(c_1449,plain,
    ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
    | ~ r1_tmap_1(X3_52,X1_52,sK5,X0_53)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X3_52) != u1_struct_0(sK4)
    | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_752])).

cnf(c_2367,plain,
    ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
    | ~ r1_tmap_1(sK4,X1_52,sK5,X0_53)
    | ~ m1_pre_topc(X0_52,sK4)
    | ~ m1_pre_topc(sK4,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_2680,plain,
    ( ~ r1_tmap_1(sK4,X0_52,sK5,X0_53)
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X0_53)
    | ~ m1_pre_topc(sK4,X1_52)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2367])).

cnf(c_3097,plain,
    ( ~ r1_tmap_1(sK4,X0_52,sK5,X0_53)
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),X0_53)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2680])).

cnf(c_3602,plain,
    ( ~ r1_tmap_1(sK4,X0_52,sK5,sK7)
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK7)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3097])).

cnf(c_3608,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0_52,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK7) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3602])).

cnf(c_3610,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3608])).

cnf(c_3461,plain,
    ( ~ r1_tmap_1(sK4,X0_52,sK5,sK6)
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK6)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3097])).

cnf(c_3462,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0_52,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK6) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3461])).

cnf(c_3464,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK6) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3462])).

cnf(c_1477,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_3457,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1484,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,X0_53,X1_53)
    | r1_tmap_1(X0_52,X1_52,X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_2424,plain,
    ( r1_tmap_1(sK3,sK1,X0_53,X1_53)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | X0_53 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | X1_53 != sK7 ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_2554,plain,
    ( r1_tmap_1(sK3,sK1,X0_53,sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | X0_53 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_3166,plain,
    ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
    | k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2554])).

cnf(c_3168,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
    | sK6 != sK7
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK6) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3166])).

cnf(c_2968,plain,
    ( k3_tmap_1(X0_52,X1_52,sK4,sK3,sK5) = k3_tmap_1(X0_52,X1_52,sK4,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_3165,plain,
    ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k3_tmap_1(sK2,sK1,sK4,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_2968])).

cnf(c_12,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_771,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_772,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_776,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_24])).

cnf(c_777,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_776])).

cnf(c_820,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
    | r1_tmap_1(X3,X1,sK5,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_777,c_10])).

cnf(c_1448,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
    | r1_tmap_1(X3_52,X1_52,sK5,X0_53)
    | ~ v1_tsep_1(X0_52,X3_52)
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X3_52) != u1_struct_0(sK4)
    | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_820])).

cnf(c_2366,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
    | r1_tmap_1(sK4,X1_52,sK5,X0_53)
    | ~ v1_tsep_1(X0_52,sK4)
    | ~ m1_pre_topc(X0_52,sK4)
    | ~ m1_pre_topc(sK4,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_2705,plain,
    ( r1_tmap_1(sK4,X0_52,sK5,X0_53)
    | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X0_53)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,X1_52)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_2978,plain,
    ( r1_tmap_1(sK4,X0_52,sK5,X0_53)
    | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),X0_53)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2705])).

cnf(c_3092,plain,
    ( r1_tmap_1(sK4,X0_52,sK5,sK6)
    | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK6)
    | ~ v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2978])).

cnf(c_3093,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK4,X0_52,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK6) != iProver_top
    | v1_tsep_1(sK3,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3092])).

cnf(c_3095,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK6) != iProver_top
    | v1_tsep_1(sK3,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3093])).

cnf(c_8,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1473,plain,
    ( ~ v1_tsep_1(X0_52,X1_52)
    | v1_tsep_1(X0_52,X2_52)
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X2_52,X1_52)
    | ~ r1_tarski(u1_struct_0(X0_52),u1_struct_0(X2_52))
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2429,plain,
    ( v1_tsep_1(sK3,X0_52)
    | ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(X0_52,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_2585,plain,
    ( v1_tsep_1(sK3,sK4)
    | ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_2586,plain,
    ( v1_tsep_1(sK3,sK4) = iProver_top
    | v1_tsep_1(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2585])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1461,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2100,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1475,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2087,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1475])).

cnf(c_2580,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2087])).

cnf(c_2549,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1482,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | m1_subset_1(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_2409,plain,
    ( m1_subset_1(X0_53,X1_53)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | X1_53 != u1_struct_0(sK3)
    | X0_53 != sK7 ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_2490,plain,
    ( m1_subset_1(sK6,X0_53)
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | X0_53 != u1_struct_0(sK3)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_2548,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_2490])).

cnf(c_2550,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK6 != sK7
    | m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2548])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_992,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_993,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_992])).

cnf(c_1064,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_430,c_993])).

cnf(c_1452,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_1064])).

cnf(c_2444,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_2445,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2444])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1472,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2379,plain,
    ( ~ m1_pre_topc(sK3,sK4)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_2380,plain,
    ( m1_pre_topc(sK3,sK4) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2379])).

cnf(c_2365,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1466,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2095,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_16,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1468,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2142,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2095,c_1468])).

cnf(c_15,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK6)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1469,negated_conjecture,
    ( r1_tmap_1(sK4,sK1,sK5,sK6)
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2093,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1469])).

cnf(c_2157,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2093,c_1468])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
    | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_54,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_53,plain,
    ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
    | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_52,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_51,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_50,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,negated_conjecture,
    ( v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_48,plain,
    ( v1_tsep_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_44,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_43,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_41,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_40,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_39,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3610,c_3464,c_3457,c_3168,c_3165,c_3095,c_2586,c_2580,c_2549,c_2550,c_2445,c_2380,c_2365,c_2142,c_2157,c_1468,c_54,c_53,c_52,c_51,c_50,c_48,c_47,c_44,c_43,c_42,c_41,c_40,c_39,c_38,c_37,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:58:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.93/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/0.99  
% 1.93/0.99  ------  iProver source info
% 1.93/0.99  
% 1.93/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.93/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/0.99  git: non_committed_changes: false
% 1.93/0.99  git: last_make_outside_of_git: false
% 1.93/0.99  
% 1.93/0.99  ------ 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options
% 1.93/0.99  
% 1.93/0.99  --out_options                           all
% 1.93/0.99  --tptp_safe_out                         true
% 1.93/0.99  --problem_path                          ""
% 1.93/0.99  --include_path                          ""
% 1.93/0.99  --clausifier                            res/vclausify_rel
% 1.93/0.99  --clausifier_options                    --mode clausify
% 1.93/0.99  --stdin                                 false
% 1.93/0.99  --stats_out                             all
% 1.93/0.99  
% 1.93/0.99  ------ General Options
% 1.93/0.99  
% 1.93/0.99  --fof                                   false
% 1.93/0.99  --time_out_real                         305.
% 1.93/0.99  --time_out_virtual                      -1.
% 1.93/0.99  --symbol_type_check                     false
% 1.93/0.99  --clausify_out                          false
% 1.93/0.99  --sig_cnt_out                           false
% 1.93/0.99  --trig_cnt_out                          false
% 1.93/0.99  --trig_cnt_out_tolerance                1.
% 1.93/0.99  --trig_cnt_out_sk_spl                   false
% 1.93/0.99  --abstr_cl_out                          false
% 1.93/0.99  
% 1.93/0.99  ------ Global Options
% 1.93/0.99  
% 1.93/0.99  --schedule                              default
% 1.93/0.99  --add_important_lit                     false
% 1.93/0.99  --prop_solver_per_cl                    1000
% 1.93/0.99  --min_unsat_core                        false
% 1.93/0.99  --soft_assumptions                      false
% 1.93/0.99  --soft_lemma_size                       3
% 1.93/0.99  --prop_impl_unit_size                   0
% 1.93/0.99  --prop_impl_unit                        []
% 1.93/0.99  --share_sel_clauses                     true
% 1.93/0.99  --reset_solvers                         false
% 1.93/0.99  --bc_imp_inh                            [conj_cone]
% 1.93/0.99  --conj_cone_tolerance                   3.
% 1.93/0.99  --extra_neg_conj                        none
% 1.93/0.99  --large_theory_mode                     true
% 1.93/0.99  --prolific_symb_bound                   200
% 1.93/0.99  --lt_threshold                          2000
% 1.93/0.99  --clause_weak_htbl                      true
% 1.93/0.99  --gc_record_bc_elim                     false
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing Options
% 1.93/0.99  
% 1.93/0.99  --preprocessing_flag                    true
% 1.93/0.99  --time_out_prep_mult                    0.1
% 1.93/0.99  --splitting_mode                        input
% 1.93/0.99  --splitting_grd                         true
% 1.93/0.99  --splitting_cvd                         false
% 1.93/0.99  --splitting_cvd_svl                     false
% 1.93/0.99  --splitting_nvd                         32
% 1.93/0.99  --sub_typing                            true
% 1.93/0.99  --prep_gs_sim                           true
% 1.93/0.99  --prep_unflatten                        true
% 1.93/0.99  --prep_res_sim                          true
% 1.93/0.99  --prep_upred                            true
% 1.93/0.99  --prep_sem_filter                       exhaustive
% 1.93/0.99  --prep_sem_filter_out                   false
% 1.93/0.99  --pred_elim                             true
% 1.93/0.99  --res_sim_input                         true
% 1.93/0.99  --eq_ax_congr_red                       true
% 1.93/0.99  --pure_diseq_elim                       true
% 1.93/0.99  --brand_transform                       false
% 1.93/0.99  --non_eq_to_eq                          false
% 1.93/0.99  --prep_def_merge                        true
% 1.93/0.99  --prep_def_merge_prop_impl              false
% 1.93/0.99  --prep_def_merge_mbd                    true
% 1.93/0.99  --prep_def_merge_tr_red                 false
% 1.93/0.99  --prep_def_merge_tr_cl                  false
% 1.93/0.99  --smt_preprocessing                     true
% 1.93/0.99  --smt_ac_axioms                         fast
% 1.93/0.99  --preprocessed_out                      false
% 1.93/0.99  --preprocessed_stats                    false
% 1.93/0.99  
% 1.93/0.99  ------ Abstraction refinement Options
% 1.93/0.99  
% 1.93/0.99  --abstr_ref                             []
% 1.93/0.99  --abstr_ref_prep                        false
% 1.93/0.99  --abstr_ref_until_sat                   false
% 1.93/0.99  --abstr_ref_sig_restrict                funpre
% 1.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.99  --abstr_ref_under                       []
% 1.93/0.99  
% 1.93/0.99  ------ SAT Options
% 1.93/0.99  
% 1.93/0.99  --sat_mode                              false
% 1.93/0.99  --sat_fm_restart_options                ""
% 1.93/0.99  --sat_gr_def                            false
% 1.93/0.99  --sat_epr_types                         true
% 1.93/0.99  --sat_non_cyclic_types                  false
% 1.93/0.99  --sat_finite_models                     false
% 1.93/0.99  --sat_fm_lemmas                         false
% 1.93/0.99  --sat_fm_prep                           false
% 1.93/0.99  --sat_fm_uc_incr                        true
% 1.93/0.99  --sat_out_model                         small
% 1.93/0.99  --sat_out_clauses                       false
% 1.93/0.99  
% 1.93/0.99  ------ QBF Options
% 1.93/0.99  
% 1.93/0.99  --qbf_mode                              false
% 1.93/0.99  --qbf_elim_univ                         false
% 1.93/0.99  --qbf_dom_inst                          none
% 1.93/0.99  --qbf_dom_pre_inst                      false
% 1.93/0.99  --qbf_sk_in                             false
% 1.93/0.99  --qbf_pred_elim                         true
% 1.93/0.99  --qbf_split                             512
% 1.93/0.99  
% 1.93/0.99  ------ BMC1 Options
% 1.93/0.99  
% 1.93/0.99  --bmc1_incremental                      false
% 1.93/0.99  --bmc1_axioms                           reachable_all
% 1.93/0.99  --bmc1_min_bound                        0
% 1.93/0.99  --bmc1_max_bound                        -1
% 1.93/0.99  --bmc1_max_bound_default                -1
% 1.93/0.99  --bmc1_symbol_reachability              true
% 1.93/0.99  --bmc1_property_lemmas                  false
% 1.93/0.99  --bmc1_k_induction                      false
% 1.93/0.99  --bmc1_non_equiv_states                 false
% 1.93/0.99  --bmc1_deadlock                         false
% 1.93/0.99  --bmc1_ucm                              false
% 1.93/0.99  --bmc1_add_unsat_core                   none
% 1.93/0.99  --bmc1_unsat_core_children              false
% 1.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.99  --bmc1_out_stat                         full
% 1.93/0.99  --bmc1_ground_init                      false
% 1.93/0.99  --bmc1_pre_inst_next_state              false
% 1.93/0.99  --bmc1_pre_inst_state                   false
% 1.93/0.99  --bmc1_pre_inst_reach_state             false
% 1.93/0.99  --bmc1_out_unsat_core                   false
% 1.93/0.99  --bmc1_aig_witness_out                  false
% 1.93/0.99  --bmc1_verbose                          false
% 1.93/0.99  --bmc1_dump_clauses_tptp                false
% 1.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.99  --bmc1_dump_file                        -
% 1.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.99  --bmc1_ucm_extend_mode                  1
% 1.93/0.99  --bmc1_ucm_init_mode                    2
% 1.93/0.99  --bmc1_ucm_cone_mode                    none
% 1.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.99  --bmc1_ucm_relax_model                  4
% 1.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.99  --bmc1_ucm_layered_model                none
% 1.93/0.99  --bmc1_ucm_max_lemma_size               10
% 1.93/0.99  
% 1.93/0.99  ------ AIG Options
% 1.93/0.99  
% 1.93/0.99  --aig_mode                              false
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation Options
% 1.93/0.99  
% 1.93/0.99  --instantiation_flag                    true
% 1.93/0.99  --inst_sos_flag                         false
% 1.93/0.99  --inst_sos_phase                        true
% 1.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel_side                     num_symb
% 1.93/0.99  --inst_solver_per_active                1400
% 1.93/0.99  --inst_solver_calls_frac                1.
% 1.93/0.99  --inst_passive_queue_type               priority_queues
% 1.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.99  --inst_passive_queues_freq              [25;2]
% 1.93/0.99  --inst_dismatching                      true
% 1.93/0.99  --inst_eager_unprocessed_to_passive     true
% 1.93/0.99  --inst_prop_sim_given                   true
% 1.93/0.99  --inst_prop_sim_new                     false
% 1.93/0.99  --inst_subs_new                         false
% 1.93/0.99  --inst_eq_res_simp                      false
% 1.93/0.99  --inst_subs_given                       false
% 1.93/0.99  --inst_orphan_elimination               true
% 1.93/0.99  --inst_learning_loop_flag               true
% 1.93/0.99  --inst_learning_start                   3000
% 1.93/0.99  --inst_learning_factor                  2
% 1.93/0.99  --inst_start_prop_sim_after_learn       3
% 1.93/0.99  --inst_sel_renew                        solver
% 1.93/0.99  --inst_lit_activity_flag                true
% 1.93/0.99  --inst_restr_to_given                   false
% 1.93/0.99  --inst_activity_threshold               500
% 1.93/0.99  --inst_out_proof                        true
% 1.93/0.99  
% 1.93/0.99  ------ Resolution Options
% 1.93/0.99  
% 1.93/0.99  --resolution_flag                       true
% 1.93/0.99  --res_lit_sel                           adaptive
% 1.93/0.99  --res_lit_sel_side                      none
% 1.93/0.99  --res_ordering                          kbo
% 1.93/0.99  --res_to_prop_solver                    active
% 1.93/0.99  --res_prop_simpl_new                    false
% 1.93/0.99  --res_prop_simpl_given                  true
% 1.93/0.99  --res_passive_queue_type                priority_queues
% 1.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.99  --res_passive_queues_freq               [15;5]
% 1.93/0.99  --res_forward_subs                      full
% 1.93/0.99  --res_backward_subs                     full
% 1.93/0.99  --res_forward_subs_resolution           true
% 1.93/0.99  --res_backward_subs_resolution          true
% 1.93/0.99  --res_orphan_elimination                true
% 1.93/0.99  --res_time_limit                        2.
% 1.93/0.99  --res_out_proof                         true
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Options
% 1.93/0.99  
% 1.93/0.99  --superposition_flag                    true
% 1.93/0.99  --sup_passive_queue_type                priority_queues
% 1.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.99  --demod_completeness_check              fast
% 1.93/0.99  --demod_use_ground                      true
% 1.93/0.99  --sup_to_prop_solver                    passive
% 1.93/0.99  --sup_prop_simpl_new                    true
% 1.93/0.99  --sup_prop_simpl_given                  true
% 1.93/0.99  --sup_fun_splitting                     false
% 1.93/0.99  --sup_smt_interval                      50000
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Simplification Setup
% 1.93/0.99  
% 1.93/0.99  --sup_indices_passive                   []
% 1.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_full_bw                           [BwDemod]
% 1.93/0.99  --sup_immed_triv                        [TrivRules]
% 1.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_immed_bw_main                     []
% 1.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  
% 1.93/0.99  ------ Combination Options
% 1.93/0.99  
% 1.93/0.99  --comb_res_mult                         3
% 1.93/0.99  --comb_sup_mult                         2
% 1.93/0.99  --comb_inst_mult                        10
% 1.93/0.99  
% 1.93/0.99  ------ Debug Options
% 1.93/0.99  
% 1.93/0.99  --dbg_backtrace                         false
% 1.93/0.99  --dbg_dump_prop_clauses                 false
% 1.93/0.99  --dbg_dump_prop_clauses_file            -
% 1.93/0.99  --dbg_out_stat                          false
% 1.93/0.99  ------ Parsing...
% 1.93/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.93/0.99  ------ Proving...
% 1.93/0.99  ------ Problem Properties 
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  clauses                                 28
% 1.93/0.99  conjectures                             18
% 1.93/0.99  EPR                                     15
% 1.93/0.99  Horn                                    22
% 1.93/0.99  unary                                   16
% 1.93/0.99  binary                                  3
% 1.93/0.99  lits                                    92
% 1.93/0.99  lits eq                                 7
% 1.93/0.99  fd_pure                                 0
% 1.93/0.99  fd_pseudo                               0
% 1.93/0.99  fd_cond                                 0
% 1.93/0.99  fd_pseudo_cond                          0
% 1.93/0.99  AC symbols                              0
% 1.93/0.99  
% 1.93/0.99  ------ Schedule dynamic 5 is on 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  ------ 
% 1.93/0.99  Current options:
% 1.93/0.99  ------ 
% 1.93/0.99  
% 1.93/0.99  ------ Input Options
% 1.93/0.99  
% 1.93/0.99  --out_options                           all
% 1.93/0.99  --tptp_safe_out                         true
% 1.93/0.99  --problem_path                          ""
% 1.93/0.99  --include_path                          ""
% 1.93/0.99  --clausifier                            res/vclausify_rel
% 1.93/0.99  --clausifier_options                    --mode clausify
% 1.93/0.99  --stdin                                 false
% 1.93/0.99  --stats_out                             all
% 1.93/0.99  
% 1.93/0.99  ------ General Options
% 1.93/0.99  
% 1.93/0.99  --fof                                   false
% 1.93/0.99  --time_out_real                         305.
% 1.93/0.99  --time_out_virtual                      -1.
% 1.93/0.99  --symbol_type_check                     false
% 1.93/0.99  --clausify_out                          false
% 1.93/0.99  --sig_cnt_out                           false
% 1.93/0.99  --trig_cnt_out                          false
% 1.93/0.99  --trig_cnt_out_tolerance                1.
% 1.93/0.99  --trig_cnt_out_sk_spl                   false
% 1.93/0.99  --abstr_cl_out                          false
% 1.93/0.99  
% 1.93/0.99  ------ Global Options
% 1.93/0.99  
% 1.93/0.99  --schedule                              default
% 1.93/0.99  --add_important_lit                     false
% 1.93/0.99  --prop_solver_per_cl                    1000
% 1.93/0.99  --min_unsat_core                        false
% 1.93/0.99  --soft_assumptions                      false
% 1.93/0.99  --soft_lemma_size                       3
% 1.93/0.99  --prop_impl_unit_size                   0
% 1.93/0.99  --prop_impl_unit                        []
% 1.93/0.99  --share_sel_clauses                     true
% 1.93/0.99  --reset_solvers                         false
% 1.93/0.99  --bc_imp_inh                            [conj_cone]
% 1.93/0.99  --conj_cone_tolerance                   3.
% 1.93/0.99  --extra_neg_conj                        none
% 1.93/0.99  --large_theory_mode                     true
% 1.93/0.99  --prolific_symb_bound                   200
% 1.93/0.99  --lt_threshold                          2000
% 1.93/0.99  --clause_weak_htbl                      true
% 1.93/0.99  --gc_record_bc_elim                     false
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing Options
% 1.93/0.99  
% 1.93/0.99  --preprocessing_flag                    true
% 1.93/0.99  --time_out_prep_mult                    0.1
% 1.93/0.99  --splitting_mode                        input
% 1.93/0.99  --splitting_grd                         true
% 1.93/0.99  --splitting_cvd                         false
% 1.93/0.99  --splitting_cvd_svl                     false
% 1.93/0.99  --splitting_nvd                         32
% 1.93/0.99  --sub_typing                            true
% 1.93/0.99  --prep_gs_sim                           true
% 1.93/0.99  --prep_unflatten                        true
% 1.93/0.99  --prep_res_sim                          true
% 1.93/0.99  --prep_upred                            true
% 1.93/0.99  --prep_sem_filter                       exhaustive
% 1.93/0.99  --prep_sem_filter_out                   false
% 1.93/0.99  --pred_elim                             true
% 1.93/0.99  --res_sim_input                         true
% 1.93/0.99  --eq_ax_congr_red                       true
% 1.93/0.99  --pure_diseq_elim                       true
% 1.93/0.99  --brand_transform                       false
% 1.93/0.99  --non_eq_to_eq                          false
% 1.93/0.99  --prep_def_merge                        true
% 1.93/0.99  --prep_def_merge_prop_impl              false
% 1.93/0.99  --prep_def_merge_mbd                    true
% 1.93/0.99  --prep_def_merge_tr_red                 false
% 1.93/0.99  --prep_def_merge_tr_cl                  false
% 1.93/0.99  --smt_preprocessing                     true
% 1.93/0.99  --smt_ac_axioms                         fast
% 1.93/0.99  --preprocessed_out                      false
% 1.93/0.99  --preprocessed_stats                    false
% 1.93/0.99  
% 1.93/0.99  ------ Abstraction refinement Options
% 1.93/0.99  
% 1.93/0.99  --abstr_ref                             []
% 1.93/0.99  --abstr_ref_prep                        false
% 1.93/0.99  --abstr_ref_until_sat                   false
% 1.93/0.99  --abstr_ref_sig_restrict                funpre
% 1.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/0.99  --abstr_ref_under                       []
% 1.93/0.99  
% 1.93/0.99  ------ SAT Options
% 1.93/0.99  
% 1.93/0.99  --sat_mode                              false
% 1.93/0.99  --sat_fm_restart_options                ""
% 1.93/0.99  --sat_gr_def                            false
% 1.93/0.99  --sat_epr_types                         true
% 1.93/0.99  --sat_non_cyclic_types                  false
% 1.93/0.99  --sat_finite_models                     false
% 1.93/0.99  --sat_fm_lemmas                         false
% 1.93/0.99  --sat_fm_prep                           false
% 1.93/0.99  --sat_fm_uc_incr                        true
% 1.93/0.99  --sat_out_model                         small
% 1.93/0.99  --sat_out_clauses                       false
% 1.93/0.99  
% 1.93/0.99  ------ QBF Options
% 1.93/0.99  
% 1.93/0.99  --qbf_mode                              false
% 1.93/0.99  --qbf_elim_univ                         false
% 1.93/0.99  --qbf_dom_inst                          none
% 1.93/0.99  --qbf_dom_pre_inst                      false
% 1.93/0.99  --qbf_sk_in                             false
% 1.93/0.99  --qbf_pred_elim                         true
% 1.93/0.99  --qbf_split                             512
% 1.93/0.99  
% 1.93/0.99  ------ BMC1 Options
% 1.93/0.99  
% 1.93/0.99  --bmc1_incremental                      false
% 1.93/0.99  --bmc1_axioms                           reachable_all
% 1.93/0.99  --bmc1_min_bound                        0
% 1.93/0.99  --bmc1_max_bound                        -1
% 1.93/0.99  --bmc1_max_bound_default                -1
% 1.93/0.99  --bmc1_symbol_reachability              true
% 1.93/0.99  --bmc1_property_lemmas                  false
% 1.93/0.99  --bmc1_k_induction                      false
% 1.93/0.99  --bmc1_non_equiv_states                 false
% 1.93/0.99  --bmc1_deadlock                         false
% 1.93/0.99  --bmc1_ucm                              false
% 1.93/0.99  --bmc1_add_unsat_core                   none
% 1.93/0.99  --bmc1_unsat_core_children              false
% 1.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/0.99  --bmc1_out_stat                         full
% 1.93/0.99  --bmc1_ground_init                      false
% 1.93/0.99  --bmc1_pre_inst_next_state              false
% 1.93/0.99  --bmc1_pre_inst_state                   false
% 1.93/0.99  --bmc1_pre_inst_reach_state             false
% 1.93/0.99  --bmc1_out_unsat_core                   false
% 1.93/0.99  --bmc1_aig_witness_out                  false
% 1.93/0.99  --bmc1_verbose                          false
% 1.93/0.99  --bmc1_dump_clauses_tptp                false
% 1.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.93/0.99  --bmc1_dump_file                        -
% 1.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.93/0.99  --bmc1_ucm_extend_mode                  1
% 1.93/0.99  --bmc1_ucm_init_mode                    2
% 1.93/0.99  --bmc1_ucm_cone_mode                    none
% 1.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.93/0.99  --bmc1_ucm_relax_model                  4
% 1.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/0.99  --bmc1_ucm_layered_model                none
% 1.93/0.99  --bmc1_ucm_max_lemma_size               10
% 1.93/0.99  
% 1.93/0.99  ------ AIG Options
% 1.93/0.99  
% 1.93/0.99  --aig_mode                              false
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation Options
% 1.93/0.99  
% 1.93/0.99  --instantiation_flag                    true
% 1.93/0.99  --inst_sos_flag                         false
% 1.93/0.99  --inst_sos_phase                        true
% 1.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/0.99  --inst_lit_sel_side                     none
% 1.93/0.99  --inst_solver_per_active                1400
% 1.93/0.99  --inst_solver_calls_frac                1.
% 1.93/0.99  --inst_passive_queue_type               priority_queues
% 1.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/0.99  --inst_passive_queues_freq              [25;2]
% 1.93/0.99  --inst_dismatching                      true
% 1.93/0.99  --inst_eager_unprocessed_to_passive     true
% 1.93/0.99  --inst_prop_sim_given                   true
% 1.93/0.99  --inst_prop_sim_new                     false
% 1.93/0.99  --inst_subs_new                         false
% 1.93/0.99  --inst_eq_res_simp                      false
% 1.93/0.99  --inst_subs_given                       false
% 1.93/0.99  --inst_orphan_elimination               true
% 1.93/0.99  --inst_learning_loop_flag               true
% 1.93/0.99  --inst_learning_start                   3000
% 1.93/0.99  --inst_learning_factor                  2
% 1.93/0.99  --inst_start_prop_sim_after_learn       3
% 1.93/0.99  --inst_sel_renew                        solver
% 1.93/0.99  --inst_lit_activity_flag                true
% 1.93/0.99  --inst_restr_to_given                   false
% 1.93/0.99  --inst_activity_threshold               500
% 1.93/0.99  --inst_out_proof                        true
% 1.93/0.99  
% 1.93/0.99  ------ Resolution Options
% 1.93/0.99  
% 1.93/0.99  --resolution_flag                       false
% 1.93/0.99  --res_lit_sel                           adaptive
% 1.93/0.99  --res_lit_sel_side                      none
% 1.93/0.99  --res_ordering                          kbo
% 1.93/0.99  --res_to_prop_solver                    active
% 1.93/0.99  --res_prop_simpl_new                    false
% 1.93/0.99  --res_prop_simpl_given                  true
% 1.93/0.99  --res_passive_queue_type                priority_queues
% 1.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/0.99  --res_passive_queues_freq               [15;5]
% 1.93/0.99  --res_forward_subs                      full
% 1.93/0.99  --res_backward_subs                     full
% 1.93/0.99  --res_forward_subs_resolution           true
% 1.93/0.99  --res_backward_subs_resolution          true
% 1.93/0.99  --res_orphan_elimination                true
% 1.93/0.99  --res_time_limit                        2.
% 1.93/0.99  --res_out_proof                         true
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Options
% 1.93/0.99  
% 1.93/0.99  --superposition_flag                    true
% 1.93/0.99  --sup_passive_queue_type                priority_queues
% 1.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.93/0.99  --demod_completeness_check              fast
% 1.93/0.99  --demod_use_ground                      true
% 1.93/0.99  --sup_to_prop_solver                    passive
% 1.93/0.99  --sup_prop_simpl_new                    true
% 1.93/0.99  --sup_prop_simpl_given                  true
% 1.93/0.99  --sup_fun_splitting                     false
% 1.93/0.99  --sup_smt_interval                      50000
% 1.93/0.99  
% 1.93/0.99  ------ Superposition Simplification Setup
% 1.93/0.99  
% 1.93/0.99  --sup_indices_passive                   []
% 1.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_full_bw                           [BwDemod]
% 1.93/0.99  --sup_immed_triv                        [TrivRules]
% 1.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_immed_bw_main                     []
% 1.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.93/0.99  
% 1.93/0.99  ------ Combination Options
% 1.93/0.99  
% 1.93/0.99  --comb_res_mult                         3
% 1.93/0.99  --comb_sup_mult                         2
% 1.93/0.99  --comb_inst_mult                        10
% 1.93/0.99  
% 1.93/0.99  ------ Debug Options
% 1.93/0.99  
% 1.93/0.99  --dbg_backtrace                         false
% 1.93/0.99  --dbg_dump_prop_clauses                 false
% 1.93/0.99  --dbg_dump_prop_clauses_file            -
% 1.93/0.99  --dbg_out_stat                          false
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  ------ Proving...
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS status Theorem for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  fof(f9,axiom,(
% 1.93/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f22,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f9])).
% 1.93/0.99  
% 1.93/0.99  fof(f23,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f22])).
% 1.93/0.99  
% 1.93/0.99  fof(f30,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.99    inference(nnf_transformation,[],[f23])).
% 1.93/0.99  
% 1.93/0.99  fof(f53,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f30])).
% 1.93/0.99  
% 1.93/0.99  fof(f80,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(equality_resolution,[],[f53])).
% 1.93/0.99  
% 1.93/0.99  fof(f8,axiom,(
% 1.93/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f20,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f8])).
% 1.93/0.99  
% 1.93/0.99  fof(f21,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f20])).
% 1.93/0.99  
% 1.93/0.99  fof(f52,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f21])).
% 1.93/0.99  
% 1.93/0.99  fof(f78,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(equality_resolution,[],[f52])).
% 1.93/0.99  
% 1.93/0.99  fof(f10,conjecture,(
% 1.93/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f11,negated_conjecture,(
% 1.93/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.93/0.99    inference(negated_conjecture,[],[f10])).
% 1.93/0.99  
% 1.93/0.99  fof(f24,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f11])).
% 1.93/0.99  
% 1.93/0.99  fof(f25,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f24])).
% 1.93/0.99  
% 1.93/0.99  fof(f31,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.93/0.99    inference(nnf_transformation,[],[f25])).
% 1.93/0.99  
% 1.93/0.99  fof(f32,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f31])).
% 1.93/0.99  
% 1.93/0.99  fof(f39,plain,(
% 1.93/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK7) | r1_tmap_1(X3,X0,X4,X5)) & sK7 = X5 & m1_subset_1(sK7,u1_struct_0(X2)))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f38,plain,(
% 1.93/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK6)) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f37,plain,(
% 1.93/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6) | ~r1_tmap_1(X3,X0,sK5,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK5),X6) | r1_tmap_1(X3,X0,sK5,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f36,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6) | ~r1_tmap_1(sK4,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK4,X2,X4),X6) | r1_tmap_1(sK4,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_pre_topc(X2,sK4) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X1) & ~v2_struct_0(sK4))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f35,plain,(
% 1.93/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK3,X0,k3_tmap_1(X1,X0,X3,sK3,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK3,X3) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f34,plain,(
% 1.93/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK2,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f33,plain,(
% 1.93/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK1,X4,X5)) & (r1_tmap_1(X2,sK1,k3_tmap_1(X1,sK1,X3,X2,X4),X6) | r1_tmap_1(X3,sK1,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f40,plain,(
% 1.93/0.99    (((((((~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK1,sK5,sK6)) & (r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK1,sK5,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f39,f38,f37,f36,f35,f34,f33])).
% 1.93/0.99  
% 1.93/0.99  fof(f66,plain,(
% 1.93/0.99    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f65,plain,(
% 1.93/0.99    v1_funct_1(sK5)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f7,axiom,(
% 1.93/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f18,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f7])).
% 1.93/0.99  
% 1.93/0.99  fof(f19,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.93/0.99    inference(flattening,[],[f18])).
% 1.93/0.99  
% 1.93/0.99  fof(f51,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f19])).
% 1.93/0.99  
% 1.93/0.99  fof(f54,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f30])).
% 1.93/0.99  
% 1.93/0.99  fof(f79,plain,(
% 1.93/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(equality_resolution,[],[f54])).
% 1.93/0.99  
% 1.93/0.99  fof(f5,axiom,(
% 1.93/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f15,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.93/0.99    inference(ennf_transformation,[],[f5])).
% 1.93/0.99  
% 1.93/0.99  fof(f16,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.93/0.99    inference(flattening,[],[f15])).
% 1.93/0.99  
% 1.93/0.99  fof(f48,plain,(
% 1.93/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f16])).
% 1.93/0.99  
% 1.93/0.99  fof(f64,plain,(
% 1.93/0.99    m1_pre_topc(sK4,sK2)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f4,axiom,(
% 1.93/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f14,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.93/0.99    inference(ennf_transformation,[],[f4])).
% 1.93/0.99  
% 1.93/0.99  fof(f47,plain,(
% 1.93/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f14])).
% 1.93/0.99  
% 1.93/0.99  fof(f2,axiom,(
% 1.93/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f45,plain,(
% 1.93/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.93/0.99    inference(cnf_transformation,[],[f2])).
% 1.93/0.99  
% 1.93/0.99  fof(f3,axiom,(
% 1.93/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f12,plain,(
% 1.93/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.93/0.99    inference(ennf_transformation,[],[f3])).
% 1.93/0.99  
% 1.93/0.99  fof(f13,plain,(
% 1.93/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.93/0.99    inference(flattening,[],[f12])).
% 1.93/0.99  
% 1.93/0.99  fof(f46,plain,(
% 1.93/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f13])).
% 1.93/0.99  
% 1.93/0.99  fof(f1,axiom,(
% 1.93/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f26,plain,(
% 1.93/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.99    inference(nnf_transformation,[],[f1])).
% 1.93/0.99  
% 1.93/0.99  fof(f27,plain,(
% 1.93/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.99    inference(rectify,[],[f26])).
% 1.93/0.99  
% 1.93/0.99  fof(f28,plain,(
% 1.93/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.93/0.99    introduced(choice_axiom,[])).
% 1.93/0.99  
% 1.93/0.99  fof(f29,plain,(
% 1.93/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 1.93/0.99  
% 1.93/0.99  fof(f41,plain,(
% 1.93/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.93/0.99    inference(cnf_transformation,[],[f29])).
% 1.93/0.99  
% 1.93/0.99  fof(f77,plain,(
% 1.93/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.93/0.99    inference(equality_resolution,[],[f41])).
% 1.93/0.99  
% 1.93/0.99  fof(f6,axiom,(
% 1.93/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.93/0.99  
% 1.93/0.99  fof(f17,plain,(
% 1.93/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.93/0.99    inference(ennf_transformation,[],[f6])).
% 1.93/0.99  
% 1.93/0.99  fof(f50,plain,(
% 1.93/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.93/0.99    inference(cnf_transformation,[],[f17])).
% 1.93/0.99  
% 1.93/0.99  fof(f71,plain,(
% 1.93/0.99    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f73,plain,(
% 1.93/0.99    sK6 = sK7),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f74,plain,(
% 1.93/0.99    r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | r1_tmap_1(sK4,sK1,sK5,sK6)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f75,plain,(
% 1.93/0.99    ~r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) | ~r1_tmap_1(sK4,sK1,sK5,sK6)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f72,plain,(
% 1.93/0.99    m1_subset_1(sK7,u1_struct_0(sK3))),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f70,plain,(
% 1.93/0.99    m1_pre_topc(sK3,sK4)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f68,plain,(
% 1.93/0.99    v1_tsep_1(sK3,sK2)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f67,plain,(
% 1.93/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f63,plain,(
% 1.93/0.99    ~v2_struct_0(sK4)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f62,plain,(
% 1.93/0.99    m1_pre_topc(sK3,sK2)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f61,plain,(
% 1.93/0.99    ~v2_struct_0(sK3)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f60,plain,(
% 1.93/0.99    l1_pre_topc(sK2)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f59,plain,(
% 1.93/0.99    v2_pre_topc(sK2)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f58,plain,(
% 1.93/0.99    ~v2_struct_0(sK2)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f57,plain,(
% 1.93/0.99    l1_pre_topc(sK1)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f56,plain,(
% 1.93/0.99    v2_pre_topc(sK1)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  fof(f55,plain,(
% 1.93/0.99    ~v2_struct_0(sK1)),
% 1.93/0.99    inference(cnf_transformation,[],[f40])).
% 1.93/0.99  
% 1.93/0.99  cnf(c_13,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ v1_tsep_1(X4,X0)
% 1.93/0.99      | ~ m1_pre_topc(X4,X5)
% 1.93/0.99      | ~ m1_pre_topc(X0,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | ~ v2_pre_topc(X5)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | v2_struct_0(X5)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X5)
% 1.93/0.99      | ~ l1_pre_topc(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_11,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ m1_pre_topc(X0,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | ~ v2_pre_topc(X5)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | v2_struct_0(X5)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | ~ l1_pre_topc(X5)
% 1.93/0.99      | ~ l1_pre_topc(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_178,plain,
% 1.93/0.99      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.93/0.99      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | ~ m1_pre_topc(X4,X5)
% 1.93/0.99      | ~ m1_pre_topc(X0,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | ~ v2_pre_topc(X5)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | v2_struct_0(X5)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X5)
% 1.93/0.99      | ~ l1_pre_topc(X1) ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_13,c_11]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_179,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ m1_pre_topc(X0,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X5)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X5)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X5) ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_178]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_23,negated_conjecture,
% 1.93/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK1)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_705,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.93/0.99      | ~ m1_pre_topc(X0,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X5)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X5)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X5)
% 1.93/0.99      | u1_struct_0(X0) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.99      | sK5 != X2 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_179,c_23]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_706,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.93/0.99      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.93/0.99      | ~ m1_pre_topc(X3,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X3)
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(sK5)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_705]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_24,negated_conjecture,
% 1.93/0.99      ( v1_funct_1(sK5) ),
% 1.93/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_710,plain,
% 1.93/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_pre_topc(X0,X3)
% 1.93/0.99      | ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | ~ m1_pre_topc(X3,X2)
% 1.93/0.99      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.93/0.99      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_706,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_711,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.93/0.99      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.93/0.99      | ~ m1_pre_topc(X3,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X3)
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_710]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_10,plain,
% 1.93/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.93/0.99      | ~ m1_pre_topc(X2,X0)
% 1.93/0.99      | m1_pre_topc(X2,X1)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_752,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.93/0.99      | ~ r1_tmap_1(X3,X1,sK5,X4)
% 1.93/0.99      | ~ m1_pre_topc(X3,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X3)
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(forward_subsumption_resolution,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_711,c_10]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1449,plain,
% 1.93/0.99      ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
% 1.93/0.99      | ~ r1_tmap_1(X3_52,X1_52,sK5,X0_53)
% 1.93/0.99      | ~ m1_pre_topc(X3_52,X2_52)
% 1.93/0.99      | ~ m1_pre_topc(X0_52,X3_52)
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 1.93/0.99      | ~ v2_pre_topc(X1_52)
% 1.93/0.99      | ~ v2_pre_topc(X2_52)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(X3_52)
% 1.93/0.99      | v2_struct_0(X1_52)
% 1.93/0.99      | v2_struct_0(X2_52)
% 1.93/0.99      | ~ l1_pre_topc(X1_52)
% 1.93/0.99      | ~ l1_pre_topc(X2_52)
% 1.93/0.99      | u1_struct_0(X3_52) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_752]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2367,plain,
% 1.93/0.99      ( r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
% 1.93/0.99      | ~ r1_tmap_1(sK4,X1_52,sK5,X0_53)
% 1.93/0.99      | ~ m1_pre_topc(X0_52,sK4)
% 1.93/0.99      | ~ m1_pre_topc(sK4,X2_52)
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
% 1.93/0.99      | ~ v2_pre_topc(X1_52)
% 1.93/0.99      | ~ v2_pre_topc(X2_52)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(X1_52)
% 1.93/0.99      | v2_struct_0(X2_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | ~ l1_pre_topc(X1_52)
% 1.93/0.99      | ~ l1_pre_topc(X2_52)
% 1.93/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1449]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2680,plain,
% 1.93/0.99      ( ~ r1_tmap_1(sK4,X0_52,sK5,X0_53)
% 1.93/0.99      | r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X0_53)
% 1.93/0.99      | ~ m1_pre_topc(sK4,X1_52)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK4)
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 1.93/0.99      | ~ v2_pre_topc(X1_52)
% 1.93/0.99      | ~ v2_pre_topc(X0_52)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(X1_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | v2_struct_0(sK3)
% 1.93/0.99      | ~ l1_pre_topc(X1_52)
% 1.93/0.99      | ~ l1_pre_topc(X0_52)
% 1.93/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2367]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3097,plain,
% 1.93/0.99      ( ~ r1_tmap_1(sK4,X0_52,sK5,X0_53)
% 1.93/0.99      | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),X0_53)
% 1.93/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK4)
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 1.93/0.99      | ~ v2_pre_topc(X0_52)
% 1.93/0.99      | ~ v2_pre_topc(sK2)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | v2_struct_0(sK2)
% 1.93/0.99      | v2_struct_0(sK3)
% 1.93/0.99      | ~ l1_pre_topc(X0_52)
% 1.93/0.99      | ~ l1_pre_topc(sK2)
% 1.93/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2680]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3602,plain,
% 1.93/0.99      ( ~ r1_tmap_1(sK4,X0_52,sK5,sK7)
% 1.93/0.99      | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK7)
% 1.93/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK4)
% 1.93/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 1.93/0.99      | ~ v2_pre_topc(X0_52)
% 1.93/0.99      | ~ v2_pre_topc(sK2)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | v2_struct_0(sK2)
% 1.93/0.99      | v2_struct_0(sK3)
% 1.93/0.99      | ~ l1_pre_topc(X0_52)
% 1.93/0.99      | ~ l1_pre_topc(sK2)
% 1.93/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_3097]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3608,plain,
% 1.93/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.93/0.99      | r1_tmap_1(sK4,X0_52,sK5,sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK7) = iProver_top
% 1.93/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52)))) != iProver_top
% 1.93/0.99      | v2_pre_topc(X0_52) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.93/0.99      | v2_struct_0(sK4) = iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.93/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_3602]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3610,plain,
% 1.93/0.99      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.93/0.99      | r1_tmap_1(sK4,sK1,sK5,sK7) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top
% 1.93/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.93/0.99      | v2_struct_0(sK4) = iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top
% 1.93/0.99      | v2_struct_0(sK1) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK2) != iProver_top
% 1.93/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_3608]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3461,plain,
% 1.93/0.99      ( ~ r1_tmap_1(sK4,X0_52,sK5,sK6)
% 1.93/0.99      | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK6)
% 1.93/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK4)
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 1.93/0.99      | ~ v2_pre_topc(X0_52)
% 1.93/0.99      | ~ v2_pre_topc(sK2)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | v2_struct_0(sK2)
% 1.93/0.99      | v2_struct_0(sK3)
% 1.93/0.99      | ~ l1_pre_topc(X0_52)
% 1.93/0.99      | ~ l1_pre_topc(sK2)
% 1.93/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_3097]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3462,plain,
% 1.93/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.93/0.99      | r1_tmap_1(sK4,X0_52,sK5,sK6) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK6) = iProver_top
% 1.93/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52)))) != iProver_top
% 1.93/0.99      | v2_pre_topc(X0_52) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.93/0.99      | v2_struct_0(sK4) = iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.93/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_3461]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3464,plain,
% 1.93/0.99      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.93/0.99      | r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK6) = iProver_top
% 1.93/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.93/0.99      | v2_struct_0(sK4) = iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top
% 1.93/0.99      | v2_struct_0(sK1) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK2) != iProver_top
% 1.93/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_3462]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1477,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3457,plain,
% 1.93/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1477]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1484,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0_52,X1_52,X0_53,X1_53)
% 1.93/0.99      | r1_tmap_1(X0_52,X1_52,X2_53,X3_53)
% 1.93/0.99      | X2_53 != X0_53
% 1.93/0.99      | X3_53 != X1_53 ),
% 1.93/0.99      theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2424,plain,
% 1.93/0.99      ( r1_tmap_1(sK3,sK1,X0_53,X1_53)
% 1.93/0.99      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
% 1.93/0.99      | X0_53 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 1.93/0.99      | X1_53 != sK7 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1484]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2554,plain,
% 1.93/0.99      ( r1_tmap_1(sK3,sK1,X0_53,sK6)
% 1.93/0.99      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
% 1.93/0.99      | X0_53 != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 1.93/0.99      | sK6 != sK7 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2424]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3166,plain,
% 1.93/0.99      ( r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK6)
% 1.93/0.99      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7)
% 1.93/0.99      | k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 1.93/0.99      | sK6 != sK7 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2554]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3168,plain,
% 1.93/0.99      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) != k3_tmap_1(sK2,sK1,sK4,sK3,sK5)
% 1.93/0.99      | sK6 != sK7
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK6) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_3166]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2968,plain,
% 1.93/0.99      ( k3_tmap_1(X0_52,X1_52,sK4,sK3,sK5) = k3_tmap_1(X0_52,X1_52,sK4,sK3,sK5) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1477]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3165,plain,
% 1.93/0.99      ( k3_tmap_1(sK2,sK1,sK4,sK3,sK5) = k3_tmap_1(sK2,sK1,sK4,sK3,sK5) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2968]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_12,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.93/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.93/0.99      | ~ v1_tsep_1(X4,X0)
% 1.93/0.99      | ~ m1_pre_topc(X4,X5)
% 1.93/0.99      | ~ m1_pre_topc(X0,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | ~ v2_pre_topc(X5)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | v2_struct_0(X5)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X5)
% 1.93/0.99      | ~ l1_pre_topc(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_771,plain,
% 1.93/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 1.93/0.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 1.93/0.99      | ~ v1_tsep_1(X4,X0)
% 1.93/0.99      | ~ m1_pre_topc(X0,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X5)
% 1.93/0.99      | ~ m1_pre_topc(X4,X0)
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.93/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(X2)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X5)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X5)
% 1.93/0.99      | v2_struct_0(X4)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X5)
% 1.93/0.99      | u1_struct_0(X0) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.93/0.99      | sK5 != X2 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_772,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.93/0.99      | r1_tmap_1(X3,X1,sK5,X4)
% 1.93/0.99      | ~ v1_tsep_1(X0,X3)
% 1.93/0.99      | ~ m1_pre_topc(X3,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X3)
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.93/0.99      | ~ v1_funct_1(sK5)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_771]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_776,plain,
% 1.93/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_pre_topc(X0,X3)
% 1.93/0.99      | ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | ~ m1_pre_topc(X3,X2)
% 1.93/0.99      | ~ v1_tsep_1(X0,X3)
% 1.93/0.99      | r1_tmap_1(X3,X1,sK5,X4)
% 1.93/0.99      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(global_propositional_subsumption,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_772,c_24]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_777,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.93/0.99      | r1_tmap_1(X3,X1,sK5,X4)
% 1.93/0.99      | ~ v1_tsep_1(X0,X3)
% 1.93/0.99      | ~ m1_pre_topc(X3,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X3)
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_776]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_820,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK5),X4)
% 1.93/0.99      | r1_tmap_1(X3,X1,sK5,X4)
% 1.93/0.99      | ~ v1_tsep_1(X0,X3)
% 1.93/0.99      | ~ m1_pre_topc(X3,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X3)
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 1.93/0.99      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | ~ v2_pre_topc(X2)
% 1.93/0.99      | v2_struct_0(X0)
% 1.93/0.99      | v2_struct_0(X3)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | ~ l1_pre_topc(X1)
% 1.93/0.99      | ~ l1_pre_topc(X2)
% 1.93/0.99      | u1_struct_0(X3) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(forward_subsumption_resolution,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_777,c_10]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1448,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,X3_52,X0_52,sK5),X0_53)
% 1.93/0.99      | r1_tmap_1(X3_52,X1_52,sK5,X0_53)
% 1.93/0.99      | ~ v1_tsep_1(X0_52,X3_52)
% 1.93/0.99      | ~ m1_pre_topc(X3_52,X2_52)
% 1.93/0.99      | ~ m1_pre_topc(X0_52,X3_52)
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X3_52))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_52),u1_struct_0(X1_52))))
% 1.93/0.99      | ~ v2_pre_topc(X1_52)
% 1.93/0.99      | ~ v2_pre_topc(X2_52)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(X3_52)
% 1.93/0.99      | v2_struct_0(X1_52)
% 1.93/0.99      | v2_struct_0(X2_52)
% 1.93/0.99      | ~ l1_pre_topc(X1_52)
% 1.93/0.99      | ~ l1_pre_topc(X2_52)
% 1.93/0.99      | u1_struct_0(X3_52) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_820]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2366,plain,
% 1.93/0.99      ( ~ r1_tmap_1(X0_52,X1_52,k3_tmap_1(X2_52,X1_52,sK4,X0_52,sK5),X0_53)
% 1.93/0.99      | r1_tmap_1(sK4,X1_52,sK5,X0_53)
% 1.93/0.99      | ~ v1_tsep_1(X0_52,sK4)
% 1.93/0.99      | ~ m1_pre_topc(X0_52,sK4)
% 1.93/0.99      | ~ m1_pre_topc(sK4,X2_52)
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_52))))
% 1.93/0.99      | ~ v2_pre_topc(X1_52)
% 1.93/0.99      | ~ v2_pre_topc(X2_52)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(X1_52)
% 1.93/0.99      | v2_struct_0(X2_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | ~ l1_pre_topc(X1_52)
% 1.93/0.99      | ~ l1_pre_topc(X2_52)
% 1.93/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1448]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2705,plain,
% 1.93/0.99      ( r1_tmap_1(sK4,X0_52,sK5,X0_53)
% 1.93/0.99      | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(X1_52,X0_52,sK4,sK3,sK5),X0_53)
% 1.93/0.99      | ~ v1_tsep_1(sK3,sK4)
% 1.93/0.99      | ~ m1_pre_topc(sK4,X1_52)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK4)
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 1.93/0.99      | ~ v2_pre_topc(X1_52)
% 1.93/0.99      | ~ v2_pre_topc(X0_52)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(X1_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | v2_struct_0(sK3)
% 1.93/0.99      | ~ l1_pre_topc(X1_52)
% 1.93/0.99      | ~ l1_pre_topc(X0_52)
% 1.93/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2366]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2978,plain,
% 1.93/0.99      ( r1_tmap_1(sK4,X0_52,sK5,X0_53)
% 1.93/0.99      | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),X0_53)
% 1.93/0.99      | ~ v1_tsep_1(sK3,sK4)
% 1.93/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK4)
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 1.93/0.99      | ~ v2_pre_topc(X0_52)
% 1.93/0.99      | ~ v2_pre_topc(sK2)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | v2_struct_0(sK2)
% 1.93/0.99      | v2_struct_0(sK3)
% 1.93/0.99      | ~ l1_pre_topc(X0_52)
% 1.93/0.99      | ~ l1_pre_topc(sK2)
% 1.93/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2705]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3092,plain,
% 1.93/0.99      ( r1_tmap_1(sK4,X0_52,sK5,sK6)
% 1.93/0.99      | ~ r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK6)
% 1.93/0.99      | ~ v1_tsep_1(sK3,sK4)
% 1.93/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK4)
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.93/0.99      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52))))
% 1.93/0.99      | ~ v2_pre_topc(X0_52)
% 1.93/0.99      | ~ v2_pre_topc(sK2)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | v2_struct_0(sK2)
% 1.93/0.99      | v2_struct_0(sK3)
% 1.93/0.99      | ~ l1_pre_topc(X0_52)
% 1.93/0.99      | ~ l1_pre_topc(sK2)
% 1.93/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2978]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3093,plain,
% 1.93/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.93/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.93/0.99      | r1_tmap_1(sK4,X0_52,sK5,sK6) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,X0_52,k3_tmap_1(sK2,X0_52,sK4,sK3,sK5),sK6) != iProver_top
% 1.93/0.99      | v1_tsep_1(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_52)))) != iProver_top
% 1.93/0.99      | v2_pre_topc(X0_52) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.93/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.93/0.99      | v2_struct_0(sK4) = iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.93/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_3092]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3095,plain,
% 1.93/0.99      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.93/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.93/0.99      | r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK6) != iProver_top
% 1.93/0.99      | v1_tsep_1(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.93/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.93/0.99      | v2_struct_0(sK4) = iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top
% 1.93/0.99      | v2_struct_0(sK1) = iProver_top
% 1.93/0.99      | v2_struct_0(sK3) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK2) != iProver_top
% 1.93/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_3093]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_8,plain,
% 1.93/0.99      ( ~ v1_tsep_1(X0,X1)
% 1.93/0.99      | v1_tsep_1(X0,X2)
% 1.93/0.99      | ~ m1_pre_topc(X0,X1)
% 1.93/0.99      | ~ m1_pre_topc(X2,X1)
% 1.93/0.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 1.93/0.99      | ~ v2_pre_topc(X1)
% 1.93/0.99      | v2_struct_0(X1)
% 1.93/0.99      | v2_struct_0(X2)
% 1.93/0.99      | ~ l1_pre_topc(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1473,plain,
% 1.93/0.99      ( ~ v1_tsep_1(X0_52,X1_52)
% 1.93/0.99      | v1_tsep_1(X0_52,X2_52)
% 1.93/0.99      | ~ m1_pre_topc(X0_52,X1_52)
% 1.93/0.99      | ~ m1_pre_topc(X2_52,X1_52)
% 1.93/0.99      | ~ r1_tarski(u1_struct_0(X0_52),u1_struct_0(X2_52))
% 1.93/0.99      | ~ v2_pre_topc(X1_52)
% 1.93/0.99      | v2_struct_0(X1_52)
% 1.93/0.99      | v2_struct_0(X2_52)
% 1.93/0.99      | ~ l1_pre_topc(X1_52) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2429,plain,
% 1.93/0.99      ( v1_tsep_1(sK3,X0_52)
% 1.93/0.99      | ~ v1_tsep_1(sK3,sK2)
% 1.93/0.99      | ~ m1_pre_topc(X0_52,sK2)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK2)
% 1.93/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52))
% 1.93/0.99      | ~ v2_pre_topc(sK2)
% 1.93/0.99      | v2_struct_0(X0_52)
% 1.93/0.99      | v2_struct_0(sK2)
% 1.93/0.99      | ~ l1_pre_topc(sK2) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1473]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2585,plain,
% 1.93/0.99      ( v1_tsep_1(sK3,sK4)
% 1.93/0.99      | ~ v1_tsep_1(sK3,sK2)
% 1.93/0.99      | ~ m1_pre_topc(sK4,sK2)
% 1.93/0.99      | ~ m1_pre_topc(sK3,sK2)
% 1.93/0.99      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4))
% 1.93/0.99      | ~ v2_pre_topc(sK2)
% 1.93/0.99      | v2_struct_0(sK4)
% 1.93/0.99      | v2_struct_0(sK2)
% 1.93/0.99      | ~ l1_pre_topc(sK2) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2429]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2586,plain,
% 1.93/0.99      ( v1_tsep_1(sK3,sK4) = iProver_top
% 1.93/0.99      | v1_tsep_1(sK3,sK2) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK4,sK2) != iProver_top
% 1.93/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 1.93/0.99      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
% 1.93/0.99      | v2_pre_topc(sK2) != iProver_top
% 1.93/0.99      | v2_struct_0(sK4) = iProver_top
% 1.93/0.99      | v2_struct_0(sK2) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2585]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_25,negated_conjecture,
% 1.93/0.99      ( m1_pre_topc(sK4,sK2) ),
% 1.93/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1461,negated_conjecture,
% 1.93/0.99      ( m1_pre_topc(sK4,sK2) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2100,plain,
% 1.93/0.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1461]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_6,plain,
% 1.93/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.93/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1475,plain,
% 1.93/0.99      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.93/0.99      | ~ l1_pre_topc(X1_52)
% 1.93/0.99      | l1_pre_topc(X0_52) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2087,plain,
% 1.93/0.99      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 1.93/0.99      | l1_pre_topc(X1_52) != iProver_top
% 1.93/0.99      | l1_pre_topc(X0_52) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1475]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2580,plain,
% 1.93/0.99      ( l1_pre_topc(sK4) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 1.93/0.99      inference(superposition,[status(thm)],[c_2100,c_2087]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2549,plain,
% 1.93/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1477]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1482,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0_53,X1_53)
% 1.93/0.99      | m1_subset_1(X2_53,X3_53)
% 1.93/0.99      | X2_53 != X0_53
% 1.93/0.99      | X3_53 != X1_53 ),
% 1.93/0.99      theory(equality) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2409,plain,
% 1.93/0.99      ( m1_subset_1(X0_53,X1_53)
% 1.93/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 1.93/0.99      | X1_53 != u1_struct_0(sK3)
% 1.93/0.99      | X0_53 != sK7 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1482]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2490,plain,
% 1.93/0.99      ( m1_subset_1(sK6,X0_53)
% 1.93/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 1.93/0.99      | X0_53 != u1_struct_0(sK3)
% 1.93/0.99      | sK6 != sK7 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2409]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2548,plain,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3))
% 1.93/0.99      | ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 1.93/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.93/0.99      | sK6 != sK7 ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_2490]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2550,plain,
% 1.93/0.99      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.93/0.99      | sK6 != sK7
% 1.93/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top
% 1.93/0.99      | m1_subset_1(sK7,u1_struct_0(sK3)) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2548]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_4,plain,
% 1.93/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_5,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_429,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 1.93/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_430,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.93/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.93/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_3,plain,
% 1.93/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f77]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_992,plain,
% 1.93/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.93/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_993,plain,
% 1.93/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.93/0.99      inference(renaming,[status(thm)],[c_992]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1064,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.93/0.99      inference(bin_hyper_res,[status(thm)],[c_430,c_993]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1452,plain,
% 1.93/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 1.93/0.99      | r1_tarski(X0_53,X1_53) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_1064]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2444,plain,
% 1.93/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.93/0.99      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1452]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2445,plain,
% 1.93/0.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 1.93/0.99      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2444]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_9,plain,
% 1.93/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.93/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.93/0.99      | ~ l1_pre_topc(X1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1472,plain,
% 1.93/0.99      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.93/0.99      | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52)))
% 1.93/0.99      | ~ l1_pre_topc(X1_52) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2379,plain,
% 1.93/0.99      ( ~ m1_pre_topc(sK3,sK4)
% 1.93/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.93/0.99      | ~ l1_pre_topc(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1472]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2380,plain,
% 1.93/0.99      ( m1_pre_topc(sK3,sK4) != iProver_top
% 1.93/0.99      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 1.93/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_2379]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2365,plain,
% 1.93/0.99      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 1.93/0.99      inference(instantiation,[status(thm)],[c_1477]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_18,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1466,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2095,plain,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_16,negated_conjecture,
% 1.93/0.99      ( sK6 = sK7 ),
% 1.93/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1468,negated_conjecture,
% 1.93/0.99      ( sK6 = sK7 ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2142,plain,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_2095,c_1468]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_15,negated_conjecture,
% 1.93/0.99      ( r1_tmap_1(sK4,sK1,sK5,sK6)
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 1.93/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_1469,negated_conjecture,
% 1.93/0.99      ( r1_tmap_1(sK4,sK1,sK5,sK6)
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 1.93/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2093,plain,
% 1.93/0.99      ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1469]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_2157,plain,
% 1.93/0.99      ( r1_tmap_1(sK4,sK1,sK5,sK7) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 1.93/0.99      inference(light_normalisation,[status(thm)],[c_2093,c_1468]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_14,negated_conjecture,
% 1.93/0.99      ( ~ r1_tmap_1(sK4,sK1,sK5,sK6)
% 1.93/0.99      | ~ r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) ),
% 1.93/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_54,plain,
% 1.93/0.99      ( r1_tmap_1(sK4,sK1,sK5,sK6) != iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_53,plain,
% 1.93/0.99      ( r1_tmap_1(sK4,sK1,sK5,sK6) = iProver_top
% 1.93/0.99      | r1_tmap_1(sK3,sK1,k3_tmap_1(sK2,sK1,sK4,sK3,sK5),sK7) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_17,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 1.93/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_52,plain,
% 1.93/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_51,plain,
% 1.93/0.99      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_19,negated_conjecture,
% 1.93/0.99      ( m1_pre_topc(sK3,sK4) ),
% 1.93/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_50,plain,
% 1.93/0.99      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_21,negated_conjecture,
% 1.93/0.99      ( v1_tsep_1(sK3,sK2) ),
% 1.93/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_48,plain,
% 1.93/0.99      ( v1_tsep_1(sK3,sK2) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_22,negated_conjecture,
% 1.93/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
% 1.93/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_47,plain,
% 1.93/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_44,plain,
% 1.93/0.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_26,negated_conjecture,
% 1.93/0.99      ( ~ v2_struct_0(sK4) ),
% 1.93/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_43,plain,
% 1.93/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_27,negated_conjecture,
% 1.93/0.99      ( m1_pre_topc(sK3,sK2) ),
% 1.93/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_42,plain,
% 1.93/0.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_28,negated_conjecture,
% 1.93/0.99      ( ~ v2_struct_0(sK3) ),
% 1.93/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_41,plain,
% 1.93/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_29,negated_conjecture,
% 1.93/0.99      ( l1_pre_topc(sK2) ),
% 1.93/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_40,plain,
% 1.93/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_30,negated_conjecture,
% 1.93/0.99      ( v2_pre_topc(sK2) ),
% 1.93/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_39,plain,
% 1.93/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_31,negated_conjecture,
% 1.93/0.99      ( ~ v2_struct_0(sK2) ),
% 1.93/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_38,plain,
% 1.93/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_32,negated_conjecture,
% 1.93/0.99      ( l1_pre_topc(sK1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_37,plain,
% 1.93/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_33,negated_conjecture,
% 1.93/0.99      ( v2_pre_topc(sK1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_36,plain,
% 1.93/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_34,negated_conjecture,
% 1.93/0.99      ( ~ v2_struct_0(sK1) ),
% 1.93/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(c_35,plain,
% 1.93/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 1.93/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.93/0.99  
% 1.93/0.99  cnf(contradiction,plain,
% 1.93/0.99      ( $false ),
% 1.93/0.99      inference(minisat,
% 1.93/0.99                [status(thm)],
% 1.93/0.99                [c_3610,c_3464,c_3457,c_3168,c_3165,c_3095,c_2586,c_2580,
% 1.93/0.99                 c_2549,c_2550,c_2445,c_2380,c_2365,c_2142,c_2157,c_1468,
% 1.93/0.99                 c_54,c_53,c_52,c_51,c_50,c_48,c_47,c_44,c_43,c_42,c_41,
% 1.93/0.99                 c_40,c_39,c_38,c_37,c_36,c_35]) ).
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.93/0.99  
% 1.93/0.99  ------                               Statistics
% 1.93/0.99  
% 1.93/0.99  ------ General
% 1.93/0.99  
% 1.93/0.99  abstr_ref_over_cycles:                  0
% 1.93/0.99  abstr_ref_under_cycles:                 0
% 1.93/0.99  gc_basic_clause_elim:                   0
% 1.93/0.99  forced_gc_time:                         0
% 1.93/0.99  parsing_time:                           0.009
% 1.93/0.99  unif_index_cands_time:                  0.
% 1.93/0.99  unif_index_add_time:                    0.
% 1.93/0.99  orderings_time:                         0.
% 1.93/0.99  out_proof_time:                         0.016
% 1.93/0.99  total_time:                             0.151
% 1.93/0.99  num_of_symbols:                         57
% 1.93/0.99  num_of_terms:                           2187
% 1.93/0.99  
% 1.93/0.99  ------ Preprocessing
% 1.93/0.99  
% 1.93/0.99  num_of_splits:                          0
% 1.93/0.99  num_of_split_atoms:                     0
% 1.93/0.99  num_of_reused_defs:                     0
% 1.93/0.99  num_eq_ax_congr_red:                    20
% 1.93/0.99  num_of_sem_filtered_clauses:            1
% 1.93/0.99  num_of_subtypes:                        2
% 1.93/0.99  monotx_restored_types:                  0
% 1.93/0.99  sat_num_of_epr_types:                   0
% 1.93/0.99  sat_num_of_non_cyclic_types:            0
% 1.93/0.99  sat_guarded_non_collapsed_types:        0
% 1.93/0.99  num_pure_diseq_elim:                    0
% 1.93/0.99  simp_replaced_by:                       0
% 1.93/0.99  res_preprocessed:                       167
% 1.93/0.99  prep_upred:                             0
% 1.93/0.99  prep_unflattend:                        24
% 1.93/0.99  smt_new_axioms:                         0
% 1.93/0.99  pred_elim_cands:                        8
% 1.93/0.99  pred_elim:                              4
% 1.93/0.99  pred_elim_cl:                           6
% 1.93/0.99  pred_elim_cycles:                       9
% 1.93/0.99  merged_defs:                            14
% 1.93/0.99  merged_defs_ncl:                        0
% 1.93/0.99  bin_hyper_res:                          15
% 1.93/0.99  prep_cycles:                            5
% 1.93/0.99  pred_elim_time:                         0.015
% 1.93/0.99  splitting_time:                         0.
% 1.93/0.99  sem_filter_time:                        0.
% 1.93/0.99  monotx_time:                            0.
% 1.93/0.99  subtype_inf_time:                       0.001
% 1.93/0.99  
% 1.93/0.99  ------ Problem properties
% 1.93/0.99  
% 1.93/0.99  clauses:                                28
% 1.93/0.99  conjectures:                            18
% 1.93/0.99  epr:                                    15
% 1.93/0.99  horn:                                   22
% 1.93/0.99  ground:                                 18
% 1.93/0.99  unary:                                  16
% 1.93/0.99  binary:                                 3
% 1.93/0.99  lits:                                   92
% 1.93/0.99  lits_eq:                                7
% 1.93/0.99  fd_pure:                                0
% 1.93/0.99  fd_pseudo:                              0
% 1.93/0.99  fd_cond:                                0
% 1.93/0.99  fd_pseudo_cond:                         0
% 1.93/0.99  ac_symbols:                             0
% 1.93/0.99  
% 1.93/0.99  ------ Propositional Solver
% 1.93/0.99  
% 1.93/0.99  prop_solver_calls:                      31
% 1.93/0.99  prop_fast_solver_calls:                 1479
% 1.93/0.99  smt_solver_calls:                       0
% 1.93/0.99  smt_fast_solver_calls:                  0
% 1.93/0.99  prop_num_of_clauses:                    705
% 1.93/0.99  prop_preprocess_simplified:             4143
% 1.93/0.99  prop_fo_subsumed:                       19
% 1.93/0.99  prop_solver_time:                       0.
% 1.93/0.99  smt_solver_time:                        0.
% 1.93/0.99  smt_fast_solver_time:                   0.
% 1.93/0.99  prop_fast_solver_time:                  0.
% 1.93/0.99  prop_unsat_core_time:                   0.
% 1.93/0.99  
% 1.93/0.99  ------ QBF
% 1.93/0.99  
% 1.93/0.99  qbf_q_res:                              0
% 1.93/0.99  qbf_num_tautologies:                    0
% 1.93/0.99  qbf_prep_cycles:                        0
% 1.93/0.99  
% 1.93/0.99  ------ BMC1
% 1.93/0.99  
% 1.93/0.99  bmc1_current_bound:                     -1
% 1.93/0.99  bmc1_last_solved_bound:                 -1
% 1.93/0.99  bmc1_unsat_core_size:                   -1
% 1.93/0.99  bmc1_unsat_core_parents_size:           -1
% 1.93/0.99  bmc1_merge_next_fun:                    0
% 1.93/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.93/0.99  
% 1.93/0.99  ------ Instantiation
% 1.93/0.99  
% 1.93/0.99  inst_num_of_clauses:                    196
% 1.93/0.99  inst_num_in_passive:                    15
% 1.93/0.99  inst_num_in_active:                     167
% 1.93/0.99  inst_num_in_unprocessed:                13
% 1.93/0.99  inst_num_of_loops:                      186
% 1.93/0.99  inst_num_of_learning_restarts:          0
% 1.93/0.99  inst_num_moves_active_passive:          14
% 1.93/0.99  inst_lit_activity:                      0
% 1.93/0.99  inst_lit_activity_moves:                0
% 1.93/0.99  inst_num_tautologies:                   0
% 1.93/0.99  inst_num_prop_implied:                  0
% 1.93/0.99  inst_num_existing_simplified:           0
% 1.93/0.99  inst_num_eq_res_simplified:             0
% 1.93/0.99  inst_num_child_elim:                    0
% 1.93/0.99  inst_num_of_dismatching_blockings:      82
% 1.93/0.99  inst_num_of_non_proper_insts:           212
% 1.93/0.99  inst_num_of_duplicates:                 0
% 1.93/0.99  inst_inst_num_from_inst_to_res:         0
% 1.93/0.99  inst_dismatching_checking_time:         0.
% 1.93/0.99  
% 1.93/0.99  ------ Resolution
% 1.93/0.99  
% 1.93/0.99  res_num_of_clauses:                     0
% 1.93/0.99  res_num_in_passive:                     0
% 1.93/0.99  res_num_in_active:                      0
% 1.93/0.99  res_num_of_loops:                       172
% 1.93/0.99  res_forward_subset_subsumed:            38
% 1.93/0.99  res_backward_subset_subsumed:           0
% 1.93/0.99  res_forward_subsumed:                   0
% 1.93/0.99  res_backward_subsumed:                  0
% 1.93/0.99  res_forward_subsumption_resolution:     2
% 1.93/0.99  res_backward_subsumption_resolution:    0
% 1.93/0.99  res_clause_to_clause_subsumption:       130
% 1.93/0.99  res_orphan_elimination:                 0
% 1.93/0.99  res_tautology_del:                      73
% 1.93/0.99  res_num_eq_res_simplified:              0
% 1.93/0.99  res_num_sel_changes:                    0
% 1.93/0.99  res_moves_from_active_to_pass:          0
% 1.93/0.99  
% 1.93/0.99  ------ Superposition
% 1.93/0.99  
% 1.93/0.99  sup_time_total:                         0.
% 1.93/0.99  sup_time_generating:                    0.
% 1.93/0.99  sup_time_sim_full:                      0.
% 1.93/0.99  sup_time_sim_immed:                     0.
% 1.93/0.99  
% 1.93/0.99  sup_num_of_clauses:                     44
% 1.93/0.99  sup_num_in_active:                      36
% 1.93/0.99  sup_num_in_passive:                     8
% 1.93/0.99  sup_num_of_loops:                       36
% 1.93/0.99  sup_fw_superposition:                   11
% 1.93/0.99  sup_bw_superposition:                   4
% 1.93/0.99  sup_immediate_simplified:               0
% 1.93/0.99  sup_given_eliminated:                   0
% 1.93/0.99  comparisons_done:                       0
% 1.93/0.99  comparisons_avoided:                    0
% 1.93/0.99  
% 1.93/0.99  ------ Simplifications
% 1.93/0.99  
% 1.93/0.99  
% 1.93/0.99  sim_fw_subset_subsumed:                 0
% 1.93/0.99  sim_bw_subset_subsumed:                 0
% 1.93/0.99  sim_fw_subsumed:                        0
% 1.93/0.99  sim_bw_subsumed:                        0
% 1.93/0.99  sim_fw_subsumption_res:                 2
% 1.93/0.99  sim_bw_subsumption_res:                 0
% 1.93/0.99  sim_tautology_del:                      2
% 1.93/0.99  sim_eq_tautology_del:                   0
% 1.93/0.99  sim_eq_res_simp:                        0
% 1.93/0.99  sim_fw_demodulated:                     0
% 1.93/0.99  sim_bw_demodulated:                     0
% 1.93/0.99  sim_light_normalised:                   3
% 1.93/0.99  sim_joinable_taut:                      0
% 1.93/0.99  sim_joinable_simp:                      0
% 1.93/0.99  sim_ac_normalised:                      0
% 1.93/0.99  sim_smt_subsumption:                    0
% 1.93/0.99  
%------------------------------------------------------------------------------
