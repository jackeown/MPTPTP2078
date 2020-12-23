%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:20 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  208 (1225 expanded)
%              Number of clauses        :  120 ( 210 expanded)
%              Number of leaves         :   21 ( 511 expanded)
%              Depth                    :   32
%              Number of atoms          : 1669 (24076 expanded)
%              Number of equality atoms :  426 (1767 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal clause size      :   46 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X0,X4,X6)
                                      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X0,X4,X6)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X0,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | ~ r1_tmap_1(X3,X0,X4,X5) )
          & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
            | r1_tmap_1(X3,X0,X4,X5) )
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6)
          | ~ r1_tmap_1(X3,X0,X4,X5) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6)
          | r1_tmap_1(X3,X0,X4,X5) )
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
              | ~ r1_tmap_1(X3,X0,X4,sK5) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
              | r1_tmap_1(X3,X0,X4,sK5) )
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6)
                  | ~ r1_tmap_1(X3,X0,sK4,X5) )
                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6)
                  | r1_tmap_1(X3,X0,sK4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_pre_topc(X2,X3)
        & m1_pre_topc(X2,X1)
        & v1_tsep_1(X2,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6)
                      | ~ r1_tmap_1(sK3,X0,X4,X5) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6)
                      | r1_tmap_1(sK3,X0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_pre_topc(X2,sK3)
            & m1_pre_topc(X2,X1)
            & v1_tsep_1(X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
                        ( ( ~ r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6)
                          | ~ r1_tmap_1(X3,X0,X4,X5) )
                        & ( r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6)
                          | r1_tmap_1(X3,X0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(sK2,X3)
                & m1_pre_topc(sK2,X1)
                & v1_tsep_1(sK2,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
                            ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X0,X4,X5) )
                            & ( r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X0,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,sK1)
                    & v1_tsep_1(X2,sK1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK0,X4,X5) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK2,sK1)
    & v1_tsep_1(sK2,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f49,f48,f47,f46,f45,f44,f43])).

fof(f79,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X7)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_16,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_14,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_14])).

cnf(c_195,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(renaming,[status(thm)],[c_194])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_786,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_26])).

cnf(c_787,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_791,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_27])).

cnf(c_792,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_791])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_833,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | ~ r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_792,c_13])).

cnf(c_2245,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK4),X4) = iProver_top
    | r1_tmap_1(X0,X1,sK4,X4) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_2685,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2245])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1508,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2521,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_2522,plain,
    ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
    | ~ r1_tmap_1(sK3,X1,sK4,X3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_2523,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_4104,plain,
    ( v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2685,c_46,c_2521,c_2523])).

cnf(c_4105,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
    | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(sK3,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4104])).

cnf(c_4125,plain,
    ( r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4105])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_38,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4529,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4125,c_38,c_39,c_40,c_50])).

cnf(c_4530,plain,
    ( r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4529])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2262,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2341,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2262,c_19])).

cnf(c_4545,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4530,c_2341])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2260,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2265,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,k1_connsp_2(X1,X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2266,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3853,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,k1_connsp_2(X1,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2266,c_2269])).

cnf(c_4273,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_3853])).

cnf(c_4283,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2260,c_4273])).

cnf(c_18,negated_conjecture,
    ( r1_tmap_1(sK3,sK0,sK4,sK5)
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2261,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2324,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2261,c_19])).

cnf(c_15,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_11,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_203,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_12])).

cnf(c_204,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_24,negated_conjecture,
    ( v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_477,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_24])).

cnf(c_478,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_480,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_33,c_32,c_30])).

cnf(c_490,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
    | ~ r2_hidden(X3,X6)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(sK2) != X6
    | sK1 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_480])).

cnf(c_491,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_495,plain,
    ( ~ v2_pre_topc(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | r1_tmap_1(X0,X1,X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_34,c_33,c_32])).

cnf(c_496,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_720,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X4,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_496,c_26])).

cnf(c_721,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,sK1)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_725,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X2,sK1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_27])).

cnf(c_726,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X2,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_725])).

cnf(c_2246,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
    | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,sK1) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r2_hidden(X3,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_43,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_45,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_727,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
    | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,sK1) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r2_hidden(X3,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_2549,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2550,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2549])).

cnf(c_3023,plain,
    ( m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X2,sK1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
    | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r2_hidden(X3,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2246,c_43,c_45,c_727,c_2550])).

cnf(c_3024,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
    | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X2,sK1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r2_hidden(X3,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3023])).

cnf(c_3046,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X2,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3024])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_47,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3051,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3046,c_46,c_47])).

cnf(c_3052,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK0)
    | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
    | m1_pre_topc(X1,sK3) != iProver_top
    | m1_pre_topc(X1,sK1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X2,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3051])).

cnf(c_3071,plain,
    ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
    | r2_hidden(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3052])).

cnf(c_2255,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2263,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3116,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2255,c_2263])).

cnf(c_42,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3502,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3116,c_42,c_43])).

cnf(c_4025,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | r2_hidden(X1,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
    | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3071,c_38,c_39,c_40,c_42,c_43,c_50,c_3116])).

cnf(c_4026,plain,
    ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
    | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4025])).

cnf(c_4039,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_4026])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_44,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_53,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_55,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2259,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2299,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2259,c_19])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3170,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3171,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3170])).

cnf(c_4097,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
    | r2_hidden(sK6,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4039,c_44,c_53,c_55,c_2299,c_3171])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3012,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3549,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3012])).

cnf(c_3550,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3549])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2691,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2878,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2691])).

cnf(c_2879,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2878])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2533,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | r2_hidden(sK6,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2534,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2533])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4545,c_4283,c_4097,c_3550,c_2879,c_2534,c_2299,c_55,c_53,c_47,c_45,c_44,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.14/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/0.99  
% 2.14/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.14/0.99  
% 2.14/0.99  ------  iProver source info
% 2.14/0.99  
% 2.14/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.14/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.14/0.99  git: non_committed_changes: false
% 2.14/0.99  git: last_make_outside_of_git: false
% 2.14/0.99  
% 2.14/0.99  ------ 
% 2.14/0.99  
% 2.14/0.99  ------ Input Options
% 2.14/0.99  
% 2.14/0.99  --out_options                           all
% 2.14/0.99  --tptp_safe_out                         true
% 2.14/0.99  --problem_path                          ""
% 2.14/0.99  --include_path                          ""
% 2.14/0.99  --clausifier                            res/vclausify_rel
% 2.14/0.99  --clausifier_options                    --mode clausify
% 2.14/0.99  --stdin                                 false
% 2.14/0.99  --stats_out                             all
% 2.14/0.99  
% 2.14/0.99  ------ General Options
% 2.14/0.99  
% 2.14/0.99  --fof                                   false
% 2.14/0.99  --time_out_real                         305.
% 2.14/0.99  --time_out_virtual                      -1.
% 2.14/0.99  --symbol_type_check                     false
% 2.14/0.99  --clausify_out                          false
% 2.14/0.99  --sig_cnt_out                           false
% 2.14/0.99  --trig_cnt_out                          false
% 2.14/0.99  --trig_cnt_out_tolerance                1.
% 2.14/0.99  --trig_cnt_out_sk_spl                   false
% 2.14/0.99  --abstr_cl_out                          false
% 2.14/0.99  
% 2.14/0.99  ------ Global Options
% 2.14/0.99  
% 2.14/0.99  --schedule                              default
% 2.14/0.99  --add_important_lit                     false
% 2.14/0.99  --prop_solver_per_cl                    1000
% 2.14/0.99  --min_unsat_core                        false
% 2.14/0.99  --soft_assumptions                      false
% 2.14/0.99  --soft_lemma_size                       3
% 2.14/0.99  --prop_impl_unit_size                   0
% 2.14/0.99  --prop_impl_unit                        []
% 2.14/0.99  --share_sel_clauses                     true
% 2.14/0.99  --reset_solvers                         false
% 2.14/0.99  --bc_imp_inh                            [conj_cone]
% 2.14/0.99  --conj_cone_tolerance                   3.
% 2.14/0.99  --extra_neg_conj                        none
% 2.14/0.99  --large_theory_mode                     true
% 2.14/0.99  --prolific_symb_bound                   200
% 2.14/0.99  --lt_threshold                          2000
% 2.14/0.99  --clause_weak_htbl                      true
% 2.14/0.99  --gc_record_bc_elim                     false
% 2.14/0.99  
% 2.14/0.99  ------ Preprocessing Options
% 2.14/0.99  
% 2.14/0.99  --preprocessing_flag                    true
% 2.14/0.99  --time_out_prep_mult                    0.1
% 2.14/0.99  --splitting_mode                        input
% 2.14/0.99  --splitting_grd                         true
% 2.14/0.99  --splitting_cvd                         false
% 2.14/0.99  --splitting_cvd_svl                     false
% 2.14/0.99  --splitting_nvd                         32
% 2.14/0.99  --sub_typing                            true
% 2.14/0.99  --prep_gs_sim                           true
% 2.14/0.99  --prep_unflatten                        true
% 2.14/0.99  --prep_res_sim                          true
% 2.14/0.99  --prep_upred                            true
% 2.14/0.99  --prep_sem_filter                       exhaustive
% 2.14/0.99  --prep_sem_filter_out                   false
% 2.14/0.99  --pred_elim                             true
% 2.14/0.99  --res_sim_input                         true
% 2.14/0.99  --eq_ax_congr_red                       true
% 2.14/0.99  --pure_diseq_elim                       true
% 2.14/0.99  --brand_transform                       false
% 2.14/0.99  --non_eq_to_eq                          false
% 2.14/0.99  --prep_def_merge                        true
% 2.14/0.99  --prep_def_merge_prop_impl              false
% 2.14/0.99  --prep_def_merge_mbd                    true
% 2.14/0.99  --prep_def_merge_tr_red                 false
% 2.14/0.99  --prep_def_merge_tr_cl                  false
% 2.14/0.99  --smt_preprocessing                     true
% 2.14/0.99  --smt_ac_axioms                         fast
% 2.14/0.99  --preprocessed_out                      false
% 2.14/0.99  --preprocessed_stats                    false
% 2.14/0.99  
% 2.14/0.99  ------ Abstraction refinement Options
% 2.14/0.99  
% 2.14/0.99  --abstr_ref                             []
% 2.14/0.99  --abstr_ref_prep                        false
% 2.14/0.99  --abstr_ref_until_sat                   false
% 2.14/0.99  --abstr_ref_sig_restrict                funpre
% 2.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/0.99  --abstr_ref_under                       []
% 2.14/0.99  
% 2.14/0.99  ------ SAT Options
% 2.14/0.99  
% 2.14/0.99  --sat_mode                              false
% 2.14/0.99  --sat_fm_restart_options                ""
% 2.14/0.99  --sat_gr_def                            false
% 2.14/0.99  --sat_epr_types                         true
% 2.14/0.99  --sat_non_cyclic_types                  false
% 2.14/0.99  --sat_finite_models                     false
% 2.14/0.99  --sat_fm_lemmas                         false
% 2.14/0.99  --sat_fm_prep                           false
% 2.14/0.99  --sat_fm_uc_incr                        true
% 2.14/0.99  --sat_out_model                         small
% 2.14/0.99  --sat_out_clauses                       false
% 2.14/0.99  
% 2.14/0.99  ------ QBF Options
% 2.14/0.99  
% 2.14/0.99  --qbf_mode                              false
% 2.14/0.99  --qbf_elim_univ                         false
% 2.14/0.99  --qbf_dom_inst                          none
% 2.14/0.99  --qbf_dom_pre_inst                      false
% 2.14/0.99  --qbf_sk_in                             false
% 2.14/0.99  --qbf_pred_elim                         true
% 2.14/0.99  --qbf_split                             512
% 2.14/0.99  
% 2.14/0.99  ------ BMC1 Options
% 2.14/0.99  
% 2.14/0.99  --bmc1_incremental                      false
% 2.14/0.99  --bmc1_axioms                           reachable_all
% 2.14/0.99  --bmc1_min_bound                        0
% 2.14/0.99  --bmc1_max_bound                        -1
% 2.14/0.99  --bmc1_max_bound_default                -1
% 2.14/0.99  --bmc1_symbol_reachability              true
% 2.14/0.99  --bmc1_property_lemmas                  false
% 2.14/0.99  --bmc1_k_induction                      false
% 2.14/0.99  --bmc1_non_equiv_states                 false
% 2.14/0.99  --bmc1_deadlock                         false
% 2.14/0.99  --bmc1_ucm                              false
% 2.14/0.99  --bmc1_add_unsat_core                   none
% 2.14/0.99  --bmc1_unsat_core_children              false
% 2.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/0.99  --bmc1_out_stat                         full
% 2.14/0.99  --bmc1_ground_init                      false
% 2.14/0.99  --bmc1_pre_inst_next_state              false
% 2.14/0.99  --bmc1_pre_inst_state                   false
% 2.14/0.99  --bmc1_pre_inst_reach_state             false
% 2.14/0.99  --bmc1_out_unsat_core                   false
% 2.14/0.99  --bmc1_aig_witness_out                  false
% 2.14/0.99  --bmc1_verbose                          false
% 2.14/0.99  --bmc1_dump_clauses_tptp                false
% 2.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.14/0.99  --bmc1_dump_file                        -
% 2.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.14/0.99  --bmc1_ucm_extend_mode                  1
% 2.14/0.99  --bmc1_ucm_init_mode                    2
% 2.14/0.99  --bmc1_ucm_cone_mode                    none
% 2.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.14/0.99  --bmc1_ucm_relax_model                  4
% 2.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/0.99  --bmc1_ucm_layered_model                none
% 2.14/0.99  --bmc1_ucm_max_lemma_size               10
% 2.14/0.99  
% 2.14/0.99  ------ AIG Options
% 2.14/0.99  
% 2.14/0.99  --aig_mode                              false
% 2.14/0.99  
% 2.14/0.99  ------ Instantiation Options
% 2.14/0.99  
% 2.14/0.99  --instantiation_flag                    true
% 2.14/0.99  --inst_sos_flag                         false
% 2.14/0.99  --inst_sos_phase                        true
% 2.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/0.99  --inst_lit_sel_side                     num_symb
% 2.14/0.99  --inst_solver_per_active                1400
% 2.14/0.99  --inst_solver_calls_frac                1.
% 2.14/0.99  --inst_passive_queue_type               priority_queues
% 2.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/0.99  --inst_passive_queues_freq              [25;2]
% 2.14/0.99  --inst_dismatching                      true
% 2.14/0.99  --inst_eager_unprocessed_to_passive     true
% 2.14/0.99  --inst_prop_sim_given                   true
% 2.14/0.99  --inst_prop_sim_new                     false
% 2.14/0.99  --inst_subs_new                         false
% 2.14/0.99  --inst_eq_res_simp                      false
% 2.14/0.99  --inst_subs_given                       false
% 2.14/0.99  --inst_orphan_elimination               true
% 2.14/0.99  --inst_learning_loop_flag               true
% 2.14/0.99  --inst_learning_start                   3000
% 2.14/0.99  --inst_learning_factor                  2
% 2.14/0.99  --inst_start_prop_sim_after_learn       3
% 2.14/0.99  --inst_sel_renew                        solver
% 2.14/0.99  --inst_lit_activity_flag                true
% 2.14/0.99  --inst_restr_to_given                   false
% 2.14/0.99  --inst_activity_threshold               500
% 2.14/0.99  --inst_out_proof                        true
% 2.14/0.99  
% 2.14/0.99  ------ Resolution Options
% 2.14/0.99  
% 2.14/0.99  --resolution_flag                       true
% 2.14/0.99  --res_lit_sel                           adaptive
% 2.14/0.99  --res_lit_sel_side                      none
% 2.14/0.99  --res_ordering                          kbo
% 2.14/0.99  --res_to_prop_solver                    active
% 2.14/0.99  --res_prop_simpl_new                    false
% 2.14/0.99  --res_prop_simpl_given                  true
% 2.14/0.99  --res_passive_queue_type                priority_queues
% 2.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/0.99  --res_passive_queues_freq               [15;5]
% 2.14/0.99  --res_forward_subs                      full
% 2.14/0.99  --res_backward_subs                     full
% 2.14/0.99  --res_forward_subs_resolution           true
% 2.14/0.99  --res_backward_subs_resolution          true
% 2.14/0.99  --res_orphan_elimination                true
% 2.14/0.99  --res_time_limit                        2.
% 2.14/0.99  --res_out_proof                         true
% 2.14/0.99  
% 2.14/0.99  ------ Superposition Options
% 2.14/0.99  
% 2.14/0.99  --superposition_flag                    true
% 2.14/0.99  --sup_passive_queue_type                priority_queues
% 2.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.14/0.99  --demod_completeness_check              fast
% 2.14/0.99  --demod_use_ground                      true
% 2.14/0.99  --sup_to_prop_solver                    passive
% 2.14/0.99  --sup_prop_simpl_new                    true
% 2.14/0.99  --sup_prop_simpl_given                  true
% 2.14/0.99  --sup_fun_splitting                     false
% 2.14/0.99  --sup_smt_interval                      50000
% 2.14/0.99  
% 2.14/0.99  ------ Superposition Simplification Setup
% 2.14/0.99  
% 2.14/0.99  --sup_indices_passive                   []
% 2.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.99  --sup_full_bw                           [BwDemod]
% 2.14/0.99  --sup_immed_triv                        [TrivRules]
% 2.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.99  --sup_immed_bw_main                     []
% 2.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.99  
% 2.14/0.99  ------ Combination Options
% 2.14/0.99  
% 2.14/0.99  --comb_res_mult                         3
% 2.14/0.99  --comb_sup_mult                         2
% 2.14/0.99  --comb_inst_mult                        10
% 2.14/0.99  
% 2.14/0.99  ------ Debug Options
% 2.14/0.99  
% 2.14/0.99  --dbg_backtrace                         false
% 2.14/0.99  --dbg_dump_prop_clauses                 false
% 2.14/0.99  --dbg_dump_prop_clauses_file            -
% 2.14/0.99  --dbg_out_stat                          false
% 2.14/0.99  ------ Parsing...
% 2.14/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.14/0.99  
% 2.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.14/0.99  
% 2.14/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.14/0.99  
% 2.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.14/0.99  ------ Proving...
% 2.14/0.99  ------ Problem Properties 
% 2.14/0.99  
% 2.14/0.99  
% 2.14/0.99  clauses                                 29
% 2.14/0.99  conjectures                             17
% 2.14/0.99  EPR                                     18
% 2.14/0.99  Horn                                    23
% 2.14/0.99  unary                                   16
% 2.14/0.99  binary                                  2
% 2.14/0.99  lits                                    89
% 2.14/0.99  lits eq                                 6
% 2.14/0.99  fd_pure                                 0
% 2.14/0.99  fd_pseudo                               0
% 2.14/0.99  fd_cond                                 0
% 2.14/0.99  fd_pseudo_cond                          1
% 2.14/0.99  AC symbols                              0
% 2.14/0.99  
% 2.14/0.99  ------ Schedule dynamic 5 is on 
% 2.14/0.99  
% 2.14/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.14/0.99  
% 2.14/0.99  
% 2.14/0.99  ------ 
% 2.14/0.99  Current options:
% 2.14/0.99  ------ 
% 2.14/0.99  
% 2.14/0.99  ------ Input Options
% 2.14/0.99  
% 2.14/0.99  --out_options                           all
% 2.14/0.99  --tptp_safe_out                         true
% 2.14/0.99  --problem_path                          ""
% 2.14/0.99  --include_path                          ""
% 2.14/0.99  --clausifier                            res/vclausify_rel
% 2.14/0.99  --clausifier_options                    --mode clausify
% 2.14/0.99  --stdin                                 false
% 2.14/0.99  --stats_out                             all
% 2.14/0.99  
% 2.14/0.99  ------ General Options
% 2.14/0.99  
% 2.14/0.99  --fof                                   false
% 2.14/0.99  --time_out_real                         305.
% 2.14/0.99  --time_out_virtual                      -1.
% 2.14/0.99  --symbol_type_check                     false
% 2.14/0.99  --clausify_out                          false
% 2.14/0.99  --sig_cnt_out                           false
% 2.14/0.99  --trig_cnt_out                          false
% 2.14/0.99  --trig_cnt_out_tolerance                1.
% 2.14/0.99  --trig_cnt_out_sk_spl                   false
% 2.14/0.99  --abstr_cl_out                          false
% 2.14/0.99  
% 2.14/0.99  ------ Global Options
% 2.14/0.99  
% 2.14/0.99  --schedule                              default
% 2.14/0.99  --add_important_lit                     false
% 2.14/0.99  --prop_solver_per_cl                    1000
% 2.14/0.99  --min_unsat_core                        false
% 2.14/0.99  --soft_assumptions                      false
% 2.14/0.99  --soft_lemma_size                       3
% 2.14/0.99  --prop_impl_unit_size                   0
% 2.14/0.99  --prop_impl_unit                        []
% 2.14/0.99  --share_sel_clauses                     true
% 2.14/0.99  --reset_solvers                         false
% 2.14/0.99  --bc_imp_inh                            [conj_cone]
% 2.14/0.99  --conj_cone_tolerance                   3.
% 2.14/0.99  --extra_neg_conj                        none
% 2.14/0.99  --large_theory_mode                     true
% 2.14/0.99  --prolific_symb_bound                   200
% 2.14/0.99  --lt_threshold                          2000
% 2.14/0.99  --clause_weak_htbl                      true
% 2.14/0.99  --gc_record_bc_elim                     false
% 2.14/0.99  
% 2.14/0.99  ------ Preprocessing Options
% 2.14/0.99  
% 2.14/0.99  --preprocessing_flag                    true
% 2.14/0.99  --time_out_prep_mult                    0.1
% 2.14/0.99  --splitting_mode                        input
% 2.14/0.99  --splitting_grd                         true
% 2.14/0.99  --splitting_cvd                         false
% 2.14/0.99  --splitting_cvd_svl                     false
% 2.14/0.99  --splitting_nvd                         32
% 2.14/0.99  --sub_typing                            true
% 2.14/0.99  --prep_gs_sim                           true
% 2.14/0.99  --prep_unflatten                        true
% 2.14/0.99  --prep_res_sim                          true
% 2.14/0.99  --prep_upred                            true
% 2.14/0.99  --prep_sem_filter                       exhaustive
% 2.14/0.99  --prep_sem_filter_out                   false
% 2.14/0.99  --pred_elim                             true
% 2.14/0.99  --res_sim_input                         true
% 2.14/0.99  --eq_ax_congr_red                       true
% 2.14/0.99  --pure_diseq_elim                       true
% 2.14/0.99  --brand_transform                       false
% 2.14/0.99  --non_eq_to_eq                          false
% 2.14/0.99  --prep_def_merge                        true
% 2.14/0.99  --prep_def_merge_prop_impl              false
% 2.14/0.99  --prep_def_merge_mbd                    true
% 2.14/0.99  --prep_def_merge_tr_red                 false
% 2.14/0.99  --prep_def_merge_tr_cl                  false
% 2.14/0.99  --smt_preprocessing                     true
% 2.14/0.99  --smt_ac_axioms                         fast
% 2.14/0.99  --preprocessed_out                      false
% 2.14/0.99  --preprocessed_stats                    false
% 2.14/0.99  
% 2.14/0.99  ------ Abstraction refinement Options
% 2.14/0.99  
% 2.14/0.99  --abstr_ref                             []
% 2.14/0.99  --abstr_ref_prep                        false
% 2.14/0.99  --abstr_ref_until_sat                   false
% 2.14/0.99  --abstr_ref_sig_restrict                funpre
% 2.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/0.99  --abstr_ref_under                       []
% 2.14/0.99  
% 2.14/0.99  ------ SAT Options
% 2.14/0.99  
% 2.14/0.99  --sat_mode                              false
% 2.14/0.99  --sat_fm_restart_options                ""
% 2.14/0.99  --sat_gr_def                            false
% 2.14/0.99  --sat_epr_types                         true
% 2.14/0.99  --sat_non_cyclic_types                  false
% 2.14/0.99  --sat_finite_models                     false
% 2.14/0.99  --sat_fm_lemmas                         false
% 2.14/0.99  --sat_fm_prep                           false
% 2.14/0.99  --sat_fm_uc_incr                        true
% 2.14/0.99  --sat_out_model                         small
% 2.14/0.99  --sat_out_clauses                       false
% 2.14/0.99  
% 2.14/0.99  ------ QBF Options
% 2.14/0.99  
% 2.14/0.99  --qbf_mode                              false
% 2.14/0.99  --qbf_elim_univ                         false
% 2.14/0.99  --qbf_dom_inst                          none
% 2.14/0.99  --qbf_dom_pre_inst                      false
% 2.14/0.99  --qbf_sk_in                             false
% 2.14/0.99  --qbf_pred_elim                         true
% 2.14/0.99  --qbf_split                             512
% 2.14/0.99  
% 2.14/0.99  ------ BMC1 Options
% 2.14/0.99  
% 2.14/0.99  --bmc1_incremental                      false
% 2.14/0.99  --bmc1_axioms                           reachable_all
% 2.14/0.99  --bmc1_min_bound                        0
% 2.14/0.99  --bmc1_max_bound                        -1
% 2.14/0.99  --bmc1_max_bound_default                -1
% 2.14/0.99  --bmc1_symbol_reachability              true
% 2.14/0.99  --bmc1_property_lemmas                  false
% 2.14/0.99  --bmc1_k_induction                      false
% 2.14/0.99  --bmc1_non_equiv_states                 false
% 2.14/0.99  --bmc1_deadlock                         false
% 2.14/0.99  --bmc1_ucm                              false
% 2.14/0.99  --bmc1_add_unsat_core                   none
% 2.14/0.99  --bmc1_unsat_core_children              false
% 2.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/0.99  --bmc1_out_stat                         full
% 2.14/0.99  --bmc1_ground_init                      false
% 2.14/0.99  --bmc1_pre_inst_next_state              false
% 2.14/0.99  --bmc1_pre_inst_state                   false
% 2.14/0.99  --bmc1_pre_inst_reach_state             false
% 2.14/0.99  --bmc1_out_unsat_core                   false
% 2.14/0.99  --bmc1_aig_witness_out                  false
% 2.14/0.99  --bmc1_verbose                          false
% 2.14/0.99  --bmc1_dump_clauses_tptp                false
% 2.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.14/0.99  --bmc1_dump_file                        -
% 2.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.14/0.99  --bmc1_ucm_extend_mode                  1
% 2.14/0.99  --bmc1_ucm_init_mode                    2
% 2.14/0.99  --bmc1_ucm_cone_mode                    none
% 2.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.14/0.99  --bmc1_ucm_relax_model                  4
% 2.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/0.99  --bmc1_ucm_layered_model                none
% 2.14/0.99  --bmc1_ucm_max_lemma_size               10
% 2.14/0.99  
% 2.14/0.99  ------ AIG Options
% 2.14/0.99  
% 2.14/0.99  --aig_mode                              false
% 2.14/0.99  
% 2.14/0.99  ------ Instantiation Options
% 2.14/0.99  
% 2.14/0.99  --instantiation_flag                    true
% 2.14/0.99  --inst_sos_flag                         false
% 2.14/0.99  --inst_sos_phase                        true
% 2.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/0.99  --inst_lit_sel_side                     none
% 2.14/0.99  --inst_solver_per_active                1400
% 2.14/0.99  --inst_solver_calls_frac                1.
% 2.14/0.99  --inst_passive_queue_type               priority_queues
% 2.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/0.99  --inst_passive_queues_freq              [25;2]
% 2.14/0.99  --inst_dismatching                      true
% 2.14/0.99  --inst_eager_unprocessed_to_passive     true
% 2.14/0.99  --inst_prop_sim_given                   true
% 2.14/0.99  --inst_prop_sim_new                     false
% 2.14/0.99  --inst_subs_new                         false
% 2.14/0.99  --inst_eq_res_simp                      false
% 2.14/0.99  --inst_subs_given                       false
% 2.14/0.99  --inst_orphan_elimination               true
% 2.14/0.99  --inst_learning_loop_flag               true
% 2.14/0.99  --inst_learning_start                   3000
% 2.14/0.99  --inst_learning_factor                  2
% 2.14/0.99  --inst_start_prop_sim_after_learn       3
% 2.14/0.99  --inst_sel_renew                        solver
% 2.14/0.99  --inst_lit_activity_flag                true
% 2.14/0.99  --inst_restr_to_given                   false
% 2.14/0.99  --inst_activity_threshold               500
% 2.14/0.99  --inst_out_proof                        true
% 2.14/0.99  
% 2.14/0.99  ------ Resolution Options
% 2.14/0.99  
% 2.14/0.99  --resolution_flag                       false
% 2.14/0.99  --res_lit_sel                           adaptive
% 2.14/0.99  --res_lit_sel_side                      none
% 2.14/0.99  --res_ordering                          kbo
% 2.14/0.99  --res_to_prop_solver                    active
% 2.14/0.99  --res_prop_simpl_new                    false
% 2.14/0.99  --res_prop_simpl_given                  true
% 2.14/0.99  --res_passive_queue_type                priority_queues
% 2.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/0.99  --res_passive_queues_freq               [15;5]
% 2.14/0.99  --res_forward_subs                      full
% 2.14/0.99  --res_backward_subs                     full
% 2.14/0.99  --res_forward_subs_resolution           true
% 2.14/0.99  --res_backward_subs_resolution          true
% 2.14/0.99  --res_orphan_elimination                true
% 2.14/0.99  --res_time_limit                        2.
% 2.14/0.99  --res_out_proof                         true
% 2.14/0.99  
% 2.14/0.99  ------ Superposition Options
% 2.14/0.99  
% 2.14/0.99  --superposition_flag                    true
% 2.14/0.99  --sup_passive_queue_type                priority_queues
% 2.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.14/0.99  --demod_completeness_check              fast
% 2.14/0.99  --demod_use_ground                      true
% 2.14/0.99  --sup_to_prop_solver                    passive
% 2.14/0.99  --sup_prop_simpl_new                    true
% 2.14/0.99  --sup_prop_simpl_given                  true
% 2.14/0.99  --sup_fun_splitting                     false
% 2.14/0.99  --sup_smt_interval                      50000
% 2.14/0.99  
% 2.14/0.99  ------ Superposition Simplification Setup
% 2.14/0.99  
% 2.14/0.99  --sup_indices_passive                   []
% 2.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.99  --sup_full_bw                           [BwDemod]
% 2.14/0.99  --sup_immed_triv                        [TrivRules]
% 2.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.99  --sup_immed_bw_main                     []
% 2.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.99  
% 2.14/0.99  ------ Combination Options
% 2.14/0.99  
% 2.14/0.99  --comb_res_mult                         3
% 2.14/0.99  --comb_sup_mult                         2
% 2.14/0.99  --comb_inst_mult                        10
% 2.14/0.99  
% 2.14/0.99  ------ Debug Options
% 2.14/0.99  
% 2.14/0.99  --dbg_backtrace                         false
% 2.14/0.99  --dbg_dump_prop_clauses                 false
% 2.14/0.99  --dbg_dump_prop_clauses_file            -
% 2.14/0.99  --dbg_out_stat                          false
% 2.14/0.99  
% 2.14/0.99  
% 2.14/0.99  
% 2.14/0.99  
% 2.14/0.99  ------ Proving...
% 2.14/0.99  
% 2.14/0.99  
% 2.14/0.99  % SZS status Theorem for theBenchmark.p
% 2.14/0.99  
% 2.14/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.14/0.99  
% 2.14/0.99  fof(f12,axiom,(
% 2.14/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 2.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.99  
% 2.14/0.99  fof(f32,plain,(
% 2.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/0.99    inference(ennf_transformation,[],[f12])).
% 2.14/0.99  
% 2.14/0.99  fof(f33,plain,(
% 2.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.99    inference(flattening,[],[f32])).
% 2.14/0.99  
% 2.14/0.99  fof(f40,plain,(
% 2.14/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/0.99    inference(nnf_transformation,[],[f33])).
% 2.14/0.99  
% 2.14/0.99  fof(f66,plain,(
% 2.14/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/0.99    inference(cnf_transformation,[],[f40])).
% 2.14/0.99  
% 2.14/0.99  fof(f96,plain,(
% 2.14/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(equality_resolution,[],[f66])).
% 2.14/1.00  
% 2.14/1.00  fof(f11,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f30,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f11])).
% 2.14/1.00  
% 2.14/1.00  fof(f31,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f30])).
% 2.14/1.00  
% 2.14/1.00  fof(f65,plain,(
% 2.14/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f31])).
% 2.14/1.00  
% 2.14/1.00  fof(f94,plain,(
% 2.14/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(equality_resolution,[],[f65])).
% 2.14/1.00  
% 2.14/1.00  fof(f13,conjecture,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f14,negated_conjecture,(
% 2.14/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.14/1.00    inference(negated_conjecture,[],[f13])).
% 2.14/1.00  
% 2.14/1.00  fof(f34,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f14])).
% 2.14/1.00  
% 2.14/1.00  fof(f35,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f34])).
% 2.14/1.00  
% 2.14/1.00  fof(f41,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/1.00    inference(nnf_transformation,[],[f35])).
% 2.14/1.00  
% 2.14/1.00  fof(f42,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f41])).
% 2.14/1.00  
% 2.14/1.00  fof(f49,plain,(
% 2.14/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK6) | r1_tmap_1(X3,X0,X4,X5)) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f48,plain,(
% 2.14/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,sK5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f47,plain,(
% 2.14/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | ~r1_tmap_1(X3,X0,sK4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK4),X6) | r1_tmap_1(X3,X0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f46,plain,(
% 2.14/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | ~r1_tmap_1(sK3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK3,X2,X4),X6) | r1_tmap_1(sK3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(X2,sK3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f45,plain,(
% 2.14/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(sK2,X0,k3_tmap_1(X1,X0,X3,sK2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,X1) & v1_tsep_1(sK2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f44,plain,(
% 2.14/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f43,plain,(
% 2.14/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.14/1.00    introduced(choice_axiom,[])).
% 2.14/1.00  
% 2.14/1.00  fof(f50,plain,(
% 2.14/1.00    (((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f42,f49,f48,f47,f46,f45,f44,f43])).
% 2.14/1.00  
% 2.14/1.00  fof(f79,plain,(
% 2.14/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f78,plain,(
% 2.14/1.00    v1_funct_1(sK4)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f10,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f28,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f10])).
% 2.14/1.00  
% 2.14/1.00  fof(f29,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f28])).
% 2.14/1.00  
% 2.14/1.00  fof(f64,plain,(
% 2.14/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f29])).
% 2.14/1.00  
% 2.14/1.00  fof(f76,plain,(
% 2.14/1.00    ~v2_struct_0(sK3)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f68,plain,(
% 2.14/1.00    ~v2_struct_0(sK0)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f69,plain,(
% 2.14/1.00    v2_pre_topc(sK0)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f70,plain,(
% 2.14/1.00    l1_pre_topc(sK0)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f80,plain,(
% 2.14/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f88,plain,(
% 2.14/1.00    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f86,plain,(
% 2.14/1.00    sK5 = sK6),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f85,plain,(
% 2.14/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f7,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f23,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f7])).
% 2.14/1.00  
% 2.14/1.00  fof(f24,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f23])).
% 2.14/1.00  
% 2.14/1.00  fof(f59,plain,(
% 2.14/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f24])).
% 2.14/1.00  
% 2.14/1.00  fof(f6,axiom,(
% 2.14/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f21,plain,(
% 2.14/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f6])).
% 2.14/1.00  
% 2.14/1.00  fof(f22,plain,(
% 2.14/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.14/1.00    inference(flattening,[],[f21])).
% 2.14/1.00  
% 2.14/1.00  fof(f58,plain,(
% 2.14/1.00    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f22])).
% 2.14/1.00  
% 2.14/1.00  fof(f3,axiom,(
% 2.14/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f17,plain,(
% 2.14/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.14/1.00    inference(ennf_transformation,[],[f3])).
% 2.14/1.00  
% 2.14/1.00  fof(f55,plain,(
% 2.14/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f17])).
% 2.14/1.00  
% 2.14/1.00  fof(f87,plain,(
% 2.14/1.00    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f67,plain,(
% 2.14/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f40])).
% 2.14/1.00  
% 2.14/1.00  fof(f95,plain,(
% 2.14/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X7) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.14/1.00    inference(equality_resolution,[],[f67])).
% 2.14/1.00  
% 2.14/1.00  fof(f8,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f25,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f8])).
% 2.14/1.00  
% 2.14/1.00  fof(f26,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f25])).
% 2.14/1.00  
% 2.14/1.00  fof(f38,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(nnf_transformation,[],[f26])).
% 2.14/1.00  
% 2.14/1.00  fof(f39,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f38])).
% 2.14/1.00  
% 2.14/1.00  fof(f60,plain,(
% 2.14/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f39])).
% 2.14/1.00  
% 2.14/1.00  fof(f93,plain,(
% 2.14/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/1.00    inference(equality_resolution,[],[f60])).
% 2.14/1.00  
% 2.14/1.00  fof(f9,axiom,(
% 2.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f27,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(ennf_transformation,[],[f9])).
% 2.14/1.00  
% 2.14/1.00  fof(f63,plain,(
% 2.14/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f27])).
% 2.14/1.00  
% 2.14/1.00  fof(f81,plain,(
% 2.14/1.00    v1_tsep_1(sK2,sK1)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f72,plain,(
% 2.14/1.00    v2_pre_topc(sK1)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f73,plain,(
% 2.14/1.00    l1_pre_topc(sK1)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f75,plain,(
% 2.14/1.00    m1_pre_topc(sK2,sK1)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f71,plain,(
% 2.14/1.00    ~v2_struct_0(sK1)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f77,plain,(
% 2.14/1.00    m1_pre_topc(sK3,sK1)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f74,plain,(
% 2.14/1.00    ~v2_struct_0(sK2)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f83,plain,(
% 2.14/1.00    m1_pre_topc(sK2,sK3)),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f84,plain,(
% 2.14/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.14/1.00    inference(cnf_transformation,[],[f50])).
% 2.14/1.00  
% 2.14/1.00  fof(f1,axiom,(
% 2.14/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f36,plain,(
% 2.14/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/1.00    inference(nnf_transformation,[],[f1])).
% 2.14/1.00  
% 2.14/1.00  fof(f37,plain,(
% 2.14/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/1.00    inference(flattening,[],[f36])).
% 2.14/1.00  
% 2.14/1.00  fof(f52,plain,(
% 2.14/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.14/1.00    inference(cnf_transformation,[],[f37])).
% 2.14/1.00  
% 2.14/1.00  fof(f89,plain,(
% 2.14/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.14/1.00    inference(equality_resolution,[],[f52])).
% 2.14/1.00  
% 2.14/1.00  fof(f4,axiom,(
% 2.14/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f18,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/1.00    inference(ennf_transformation,[],[f4])).
% 2.14/1.00  
% 2.14/1.00  fof(f19,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/1.00    inference(flattening,[],[f18])).
% 2.14/1.00  
% 2.14/1.00  fof(f56,plain,(
% 2.14/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f19])).
% 2.14/1.00  
% 2.14/1.00  fof(f5,axiom,(
% 2.14/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f20,plain,(
% 2.14/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.14/1.00    inference(ennf_transformation,[],[f5])).
% 2.14/1.00  
% 2.14/1.00  fof(f57,plain,(
% 2.14/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f20])).
% 2.14/1.00  
% 2.14/1.00  fof(f2,axiom,(
% 2.14/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.14/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/1.00  
% 2.14/1.00  fof(f15,plain,(
% 2.14/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.14/1.00    inference(ennf_transformation,[],[f2])).
% 2.14/1.00  
% 2.14/1.00  fof(f16,plain,(
% 2.14/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.14/1.00    inference(flattening,[],[f15])).
% 2.14/1.00  
% 2.14/1.00  fof(f54,plain,(
% 2.14/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.14/1.00    inference(cnf_transformation,[],[f16])).
% 2.14/1.00  
% 2.14/1.00  cnf(c_16,plain,
% 2.14/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ v3_pre_topc(X6,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X0,X5)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
% 2.14/1.00      | ~ r2_hidden(X3,X6)
% 2.14/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X5)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X5)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X5) ),
% 2.14/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_14,plain,
% 2.14/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ m1_pre_topc(X0,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X4,X5)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X5)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | ~ l1_pre_topc(X5)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X5)
% 2.14/1.00      | ~ v2_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_194,plain,
% 2.14/1.00      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_pre_topc(X0,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X4,X5)
% 2.14/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X5)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X5)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X5) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_16,c_14]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_195,plain,
% 2.14/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ m1_pre_topc(X0,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X4,X5)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X5)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X5)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X5) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_194]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_26,negated_conjecture,
% 2.14/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
% 2.14/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_786,plain,
% 2.14/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ m1_pre_topc(X0,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X4,X5)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X5)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X5)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X5)
% 2.14/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.14/1.00      | sK4 != X2 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_195,c_26]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_787,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.14/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.14/1.00      | ~ m1_pre_topc(X3,X2)
% 2.14/1.00      | ~ m1_pre_topc(X0,X3)
% 2.14/1.00      | ~ m1_pre_topc(X0,X2)
% 2.14/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/1.00      | ~ v1_funct_1(sK4)
% 2.14/1.00      | v2_struct_0(X3)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X2)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X2)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X2)
% 2.14/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_786]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_27,negated_conjecture,
% 2.14/1.00      ( v1_funct_1(sK4) ),
% 2.14/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_791,plain,
% 2.14/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_pre_topc(X0,X2)
% 2.14/1.00      | ~ m1_pre_topc(X0,X3)
% 2.14/1.00      | ~ m1_pre_topc(X3,X2)
% 2.14/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.14/1.00      | r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.14/1.00      | v2_struct_0(X3)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X2)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X2)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X2)
% 2.14/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_787,c_27]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_792,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.14/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.14/1.00      | ~ m1_pre_topc(X3,X2)
% 2.14/1.00      | ~ m1_pre_topc(X0,X2)
% 2.14/1.00      | ~ m1_pre_topc(X0,X3)
% 2.14/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X2)
% 2.14/1.00      | v2_struct_0(X3)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X2)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X2)
% 2.14/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_791]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_13,plain,
% 2.14/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.14/1.00      | ~ m1_pre_topc(X2,X0)
% 2.14/1.00      | m1_pre_topc(X2,X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_833,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 2.14/1.00      | ~ r1_tmap_1(X3,X1,sK4,X4)
% 2.14/1.00      | ~ m1_pre_topc(X3,X2)
% 2.14/1.00      | ~ m1_pre_topc(X0,X3)
% 2.14/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.14/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X2)
% 2.14/1.00      | v2_struct_0(X3)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X2)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X2)
% 2.14/1.00      | u1_struct_0(X3) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.14/1.00      inference(forward_subsumption_resolution,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_792,c_13]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2245,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X2,X1,k3_tmap_1(X3,X1,X0,X2,sK4),X4) = iProver_top
% 2.14/1.00      | r1_tmap_1(X0,X1,sK4,X4) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,X3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.14/1.00      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | m1_subset_1(X4,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X2) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(X3) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | l1_pre_topc(X3) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X3) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2685,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,X2) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(X2) = iProver_top
% 2.14/1.00      | v2_struct_0(sK3) = iProver_top
% 2.14/1.00      | l1_pre_topc(X0) != iProver_top
% 2.14/1.00      | l1_pre_topc(X2) != iProver_top
% 2.14/1.00      | v2_pre_topc(X0) != iProver_top
% 2.14/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.14/1.00      inference(equality_resolution,[status(thm)],[c_2245]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_29,negated_conjecture,
% 2.14/1.00      ( ~ v2_struct_0(sK3) ),
% 2.14/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_46,plain,
% 2.14/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1508,plain,( X0 = X0 ),theory(equality) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2521,plain,
% 2.14/1.00      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_1508]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2522,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK3,X0,sK4),X3)
% 2.14/1.00      | ~ r1_tmap_1(sK3,X1,sK4,X3)
% 2.14/1.00      | ~ m1_pre_topc(X0,sK3)
% 2.14/1.00      | ~ m1_pre_topc(sK3,X2)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 2.14/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X2)
% 2.14/1.00      | v2_struct_0(sK3)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X2)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X2)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.14/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_833]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2523,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.14/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 2.14/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,X2) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X2) = iProver_top
% 2.14/1.00      | v2_struct_0(sK3) = iProver_top
% 2.14/1.00      | l1_pre_topc(X0) != iProver_top
% 2.14/1.00      | l1_pre_topc(X2) != iProver_top
% 2.14/1.00      | v2_pre_topc(X0) != iProver_top
% 2.14/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_2522]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4104,plain,
% 2.14/1.00      ( v2_struct_0(X2) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,X2) != iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
% 2.14/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
% 2.14/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.14/1.00      | l1_pre_topc(X0) != iProver_top
% 2.14/1.00      | l1_pre_topc(X2) != iProver_top
% 2.14/1.00      | v2_pre_topc(X0) != iProver_top
% 2.14/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_2685,c_46,c_2521,c_2523]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4105,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(X2,X0,sK3,X1,sK4),X3) = iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,X0,sK4,X3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,X2) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(X2) = iProver_top
% 2.14/1.00      | l1_pre_topc(X0) != iProver_top
% 2.14/1.00      | l1_pre_topc(X2) != iProver_top
% 2.14/1.00      | v2_pre_topc(X0) != iProver_top
% 2.14/1.00      | v2_pre_topc(X2) != iProver_top ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_4104]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4125,plain,
% 2.14/1.00      ( r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,X1) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(sK0) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.14/1.00      inference(equality_resolution,[status(thm)],[c_4105]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_37,negated_conjecture,
% 2.14/1.00      ( ~ v2_struct_0(sK0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_38,plain,
% 2.14/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_36,negated_conjecture,
% 2.14/1.00      ( v2_pre_topc(sK0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_39,plain,
% 2.14/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_35,negated_conjecture,
% 2.14/1.00      ( l1_pre_topc(sK0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_40,plain,
% 2.14/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_25,negated_conjecture,
% 2.14/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
% 2.14/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_50,plain,
% 2.14/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4529,plain,
% 2.14/1.00      ( v2_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,X1) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_4125,c_38,c_39,c_40,c_50]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4530,plain,
% 2.14/1.00      ( r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),X2) = iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,sK0,sK4,X2) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,X1) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_4529]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_17,negated_conjecture,
% 2.14/1.00      ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.14/1.00      | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.14/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2262,plain,
% 2.14/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK5) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_19,negated_conjecture,
% 2.14/1.00      ( sK5 = sK6 ),
% 2.14/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2341,plain,
% 2.14/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) != iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_2262,c_19]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4545,plain,
% 2.14/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK6) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.14/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | v2_struct_0(sK1) = iProver_top
% 2.14/1.00      | v2_struct_0(sK2) = iProver_top
% 2.14/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.14/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_4530,c_2341]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_20,negated_conjecture,
% 2.14/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.14/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2260,plain,
% 2.14/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_8,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.14/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2265,plain,
% 2.14/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0)) = iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_7,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.14/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2266,plain,
% 2.14/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.14/1.00      | ~ r2_hidden(X2,X0)
% 2.14/1.00      | ~ v1_xboole_0(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2269,plain,
% 2.14/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.14/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.14/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3853,plain,
% 2.14/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | r2_hidden(X2,k1_connsp_2(X1,X0)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top
% 2.14/1.00      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_2266,c_2269]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4273,plain,
% 2.14/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top
% 2.14/1.00      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_2265,c_3853]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4283,plain,
% 2.14/1.00      ( v2_struct_0(sK2) = iProver_top
% 2.14/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.14/1.00      | v2_pre_topc(sK2) != iProver_top
% 2.14/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_2260,c_4273]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_18,negated_conjecture,
% 2.14/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK5)
% 2.14/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
% 2.14/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2261,plain,
% 2.14/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK5) = iProver_top
% 2.14/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2324,plain,
% 2.14/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.14/1.00      | r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) = iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_2261,c_19]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_15,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ v3_pre_topc(X6,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X0,X5)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
% 2.14/1.00      | ~ r2_hidden(X3,X6)
% 2.14/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X5)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X5)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X5) ),
% 2.14/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_11,plain,
% 2.14/1.00      ( ~ v1_tsep_1(X0,X1)
% 2.14/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.14/1.00      | ~ m1_pre_topc(X0,X1)
% 2.14/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_12,plain,
% 2.14/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.14/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/1.00      | ~ l1_pre_topc(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_203,plain,
% 2.14/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.14/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.14/1.00      | ~ v1_tsep_1(X0,X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_11,c_12]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_204,plain,
% 2.14/1.00      ( ~ v1_tsep_1(X0,X1)
% 2.14/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.14/1.00      | ~ m1_pre_topc(X0,X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_203]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_24,negated_conjecture,
% 2.14/1.00      ( v1_tsep_1(sK2,sK1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_477,plain,
% 2.14/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.14/1.00      | ~ m1_pre_topc(X0,X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | sK1 != X1
% 2.14/1.00      | sK2 != X0 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_204,c_24]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_478,plain,
% 2.14/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.14/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.14/1.00      | ~ l1_pre_topc(sK1)
% 2.14/1.00      | ~ v2_pre_topc(sK1) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_33,negated_conjecture,
% 2.14/1.00      ( v2_pre_topc(sK1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_32,negated_conjecture,
% 2.14/1.00      ( l1_pre_topc(sK1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_30,negated_conjecture,
% 2.14/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_480,plain,
% 2.14/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_478,c_33,c_32,c_30]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_490,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ m1_pre_topc(X0,X5)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X4,X5)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
% 2.14/1.00      | ~ r2_hidden(X3,X6)
% 2.14/1.00      | ~ r1_tarski(X6,u1_struct_0(X4))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X5)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(X5)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X5)
% 2.14/1.00      | u1_struct_0(sK2) != X6
% 2.14/1.00      | sK1 != X5 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_480]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_491,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X0,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X4,sK1)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.00      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 2.14/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | v2_struct_0(sK1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ l1_pre_topc(sK1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(sK1) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_34,negated_conjecture,
% 2.14/1.00      ( ~ v2_struct_0(sK1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_495,plain,
% 2.14/1.00      ( ~ v2_pre_topc(X1)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 2.14/1.00      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 2.14/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_pre_topc(X4,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X0,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 2.14/1.00      | r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | ~ l1_pre_topc(X1) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_491,c_34,c_33,c_32]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_496,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X0,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X4,sK1)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.00      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 2.14/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_495]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_720,plain,
% 2.14/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.14/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(sK1,X1,X0,X4,X2),X3)
% 2.14/1.00      | ~ m1_pre_topc(X4,X0)
% 2.14/1.00      | ~ m1_pre_topc(X0,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X4,sK1)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.00      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 2.14/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X4))
% 2.14/1.00      | ~ v1_funct_1(X2)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X4)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.14/1.00      | sK4 != X2 ),
% 2.14/1.00      inference(resolution_lifted,[status(thm)],[c_496,c_26]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_721,plain,
% 2.14/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
% 2.14/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 2.14/1.00      | ~ m1_pre_topc(X0,X2)
% 2.14/1.00      | ~ m1_pre_topc(X2,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X0,sK1)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.14/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.14/1.00      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 2.14/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.14/1.00      | ~ v1_funct_1(sK4)
% 2.14/1.00      | v2_struct_0(X2)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.14/1.00      inference(unflattening,[status(thm)],[c_720]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_725,plain,
% 2.14/1.00      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.14/1.00      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 2.14/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.14/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_pre_topc(X0,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X2,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X0,X2)
% 2.14/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 2.14/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
% 2.14/1.00      | v2_struct_0(X2)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_721,c_27]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_726,plain,
% 2.14/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(sK1,X1,X2,X0,sK4),X3)
% 2.14/1.00      | r1_tmap_1(X2,X1,sK4,X3)
% 2.14/1.00      | ~ m1_pre_topc(X0,X2)
% 2.14/1.00      | ~ m1_pre_topc(X0,sK1)
% 2.14/1.00      | ~ m1_pre_topc(X2,sK1)
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.14/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.14/1.00      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.14/1.00      | ~ r2_hidden(X3,u1_struct_0(sK2))
% 2.14/1.00      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
% 2.14/1.00      | v2_struct_0(X0)
% 2.14/1.00      | v2_struct_0(X1)
% 2.14/1.00      | v2_struct_0(X2)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | u1_struct_0(X2) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_725]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2246,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
% 2.14/1.00      | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
% 2.14/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.14/1.00      | m1_pre_topc(X2,sK1) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.14/1.00      | r2_hidden(X3,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X2) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_43,plain,
% 2.14/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_45,plain,
% 2.14/1.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_727,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
% 2.14/1.00      | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
% 2.14/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.14/1.00      | m1_pre_topc(X2,sK1) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.14/1.00      | r2_hidden(X3,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X2) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2549,plain,
% 2.14/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.14/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.14/1.00      | ~ l1_pre_topc(sK1) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2550,plain,
% 2.14/1.00      ( m1_pre_topc(sK2,sK1) != iProver_top
% 2.14/1.00      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.14/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_2549]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3023,plain,
% 2.14/1.00      ( m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.14/1.00      | m1_pre_topc(X2,sK1) != iProver_top
% 2.14/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.14/1.00      | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
% 2.14/1.00      | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.14/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.14/1.00      | r2_hidden(X3,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X2) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_2246,c_43,c_45,c_727,c_2550]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3024,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 2.14/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X0,X2,sK4),X3) != iProver_top
% 2.14/1.00      | r1_tmap_1(X0,X1,sK4,X3) = iProver_top
% 2.14/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.14/1.00      | m1_pre_topc(X2,sK1) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.14/1.00      | r2_hidden(X3,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X2)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(X2) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_3023]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3046,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK1) != iProver_top
% 2.14/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.14/1.00      | r2_hidden(X2,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(sK3) = iProver_top
% 2.14/1.00      | l1_pre_topc(X0) != iProver_top
% 2.14/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.14/1.00      inference(equality_resolution,[status(thm)],[c_3024]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_28,negated_conjecture,
% 2.14/1.00      ( m1_pre_topc(sK3,sK1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_47,plain,
% 2.14/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3051,plain,
% 2.14/1.00      ( v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | r2_hidden(X2,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | u1_struct_0(X0) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK1) != iProver_top
% 2.14/1.00      | l1_pre_topc(X0) != iProver_top
% 2.14/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_3046,c_46,c_47]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3052,plain,
% 2.14/1.00      ( u1_struct_0(X0) != u1_struct_0(sK0)
% 2.14/1.00      | r1_tmap_1(X1,X0,k3_tmap_1(sK1,X0,sK3,X1,sK4),X2) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,X0,sK4,X2) = iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X1,sK1) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) != iProver_top
% 2.14/1.00      | r2_hidden(X2,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
% 2.14/1.00      | v2_struct_0(X1) = iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | l1_pre_topc(X0) != iProver_top
% 2.14/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_3051]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3071,plain,
% 2.14/1.00      ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK1) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) != iProver_top
% 2.14/1.00      | r2_hidden(X1,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top
% 2.14/1.00      | v2_struct_0(sK0) = iProver_top
% 2.14/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.14/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.14/1.00      inference(equality_resolution,[status(thm)],[c_3052]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2255,plain,
% 2.14/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2263,plain,
% 2.14/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 2.14/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 2.14/1.00      | m1_pre_topc(X2,X1) = iProver_top
% 2.14/1.00      | l1_pre_topc(X1) != iProver_top
% 2.14/1.00      | v2_pre_topc(X1) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3116,plain,
% 2.14/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK1) = iProver_top
% 2.14/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.14/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_2255,c_2263]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_42,plain,
% 2.14/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3502,plain,
% 2.14/1.00      ( m1_pre_topc(X0,sK3) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK1) = iProver_top ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_3116,c_42,c_43]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4025,plain,
% 2.14/1.00      ( v2_struct_0(X0) = iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | r2_hidden(X1,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
% 2.14/1.00      | r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_3071,c_38,c_39,c_40,c_42,c_43,c_50,c_3116]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4026,plain,
% 2.14/1.00      ( r1_tmap_1(X0,sK0,k3_tmap_1(sK1,sK0,sK3,X0,sK4),X1) != iProver_top
% 2.14/1.00      | r1_tmap_1(sK3,sK0,sK4,X1) = iProver_top
% 2.14/1.00      | m1_pre_topc(X0,sK3) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | r2_hidden(X1,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 2.14/1.00      | v2_struct_0(X0) = iProver_top ),
% 2.14/1.00      inference(renaming,[status(thm)],[c_4025]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4039,plain,
% 2.14/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.14/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.14/1.00      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 2.14/1.00      | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r2_hidden(sK6,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | v2_struct_0(sK2) = iProver_top ),
% 2.14/1.00      inference(superposition,[status(thm)],[c_2324,c_4026]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_31,negated_conjecture,
% 2.14/1.00      ( ~ v2_struct_0(sK2) ),
% 2.14/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_44,plain,
% 2.14/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_22,negated_conjecture,
% 2.14/1.00      ( m1_pre_topc(sK2,sK3) ),
% 2.14/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_53,plain,
% 2.14/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_55,plain,
% 2.14/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_21,negated_conjecture,
% 2.14/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.14/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2259,plain,
% 2.14/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2299,plain,
% 2.14/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 2.14/1.00      inference(light_normalisation,[status(thm)],[c_2259,c_19]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_1,plain,
% 2.14/1.00      ( r1_tarski(X0,X0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3170,plain,
% 2.14/1.00      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3171,plain,
% 2.14/1.00      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_3170]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_4097,plain,
% 2.14/1.00      ( r1_tmap_1(sK3,sK0,sK4,sK6) = iProver_top
% 2.14/1.00      | r2_hidden(sK6,u1_struct_0(sK2)) != iProver_top ),
% 2.14/1.00      inference(global_propositional_subsumption,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_4039,c_44,c_53,c_55,c_2299,c_3171]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_5,plain,
% 2.14/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.14/1.00      | ~ l1_pre_topc(X1)
% 2.14/1.00      | ~ v2_pre_topc(X1)
% 2.14/1.00      | v2_pre_topc(X0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3012,plain,
% 2.14/1.00      ( ~ m1_pre_topc(sK2,X0)
% 2.14/1.00      | ~ l1_pre_topc(X0)
% 2.14/1.00      | ~ v2_pre_topc(X0)
% 2.14/1.00      | v2_pre_topc(sK2) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3549,plain,
% 2.14/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.14/1.00      | ~ l1_pre_topc(sK1)
% 2.14/1.00      | ~ v2_pre_topc(sK1)
% 2.14/1.00      | v2_pre_topc(sK2) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_3012]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3550,plain,
% 2.14/1.00      ( m1_pre_topc(sK2,sK1) != iProver_top
% 2.14/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.14/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.14/1.00      | v2_pre_topc(sK2) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_3549]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_6,plain,
% 2.14/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.14/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2691,plain,
% 2.14/1.00      ( ~ m1_pre_topc(sK2,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK2) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2878,plain,
% 2.14/1.00      ( ~ m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_2691]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2879,plain,
% 2.14/1.00      ( m1_pre_topc(sK2,sK1) != iProver_top
% 2.14/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.14/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_2878]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_3,plain,
% 2.14/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.14/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2533,plain,
% 2.14/1.00      ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
% 2.14/1.00      | r2_hidden(sK6,u1_struct_0(sK2))
% 2.14/1.00      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.14/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_2534,plain,
% 2.14/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
% 2.14/1.00      | r2_hidden(sK6,u1_struct_0(sK2)) = iProver_top
% 2.14/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_2533]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(c_41,plain,
% 2.14/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.14/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.14/1.00  
% 2.14/1.00  cnf(contradiction,plain,
% 2.14/1.00      ( $false ),
% 2.14/1.00      inference(minisat,
% 2.14/1.00                [status(thm)],
% 2.14/1.00                [c_4545,c_4283,c_4097,c_3550,c_2879,c_2534,c_2299,c_55,
% 2.14/1.00                 c_53,c_47,c_45,c_44,c_43,c_42,c_41]) ).
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.14/1.00  
% 2.14/1.00  ------                               Statistics
% 2.14/1.00  
% 2.14/1.00  ------ General
% 2.14/1.00  
% 2.14/1.00  abstr_ref_over_cycles:                  0
% 2.14/1.00  abstr_ref_under_cycles:                 0
% 2.14/1.00  gc_basic_clause_elim:                   0
% 2.14/1.00  forced_gc_time:                         0
% 2.14/1.00  parsing_time:                           0.012
% 2.14/1.00  unif_index_cands_time:                  0.
% 2.14/1.00  unif_index_add_time:                    0.
% 2.14/1.00  orderings_time:                         0.
% 2.14/1.00  out_proof_time:                         0.014
% 2.14/1.00  total_time:                             0.19
% 2.14/1.00  num_of_symbols:                         56
% 2.14/1.00  num_of_terms:                           2602
% 2.14/1.00  
% 2.14/1.00  ------ Preprocessing
% 2.14/1.00  
% 2.14/1.00  num_of_splits:                          0
% 2.14/1.00  num_of_split_atoms:                     0
% 2.14/1.00  num_of_reused_defs:                     0
% 2.14/1.00  num_eq_ax_congr_red:                    14
% 2.14/1.00  num_of_sem_filtered_clauses:            1
% 2.14/1.00  num_of_subtypes:                        0
% 2.14/1.00  monotx_restored_types:                  0
% 2.14/1.00  sat_num_of_epr_types:                   0
% 2.14/1.00  sat_num_of_non_cyclic_types:            0
% 2.14/1.00  sat_guarded_non_collapsed_types:        0
% 2.14/1.00  num_pure_diseq_elim:                    0
% 2.14/1.00  simp_replaced_by:                       0
% 2.14/1.00  res_preprocessed:                       151
% 2.14/1.00  prep_upred:                             0
% 2.14/1.00  prep_unflattend:                        28
% 2.14/1.00  smt_new_axioms:                         0
% 2.14/1.00  pred_elim_cands:                        9
% 2.14/1.00  pred_elim:                              4
% 2.14/1.00  pred_elim_cl:                           6
% 2.14/1.00  pred_elim_cycles:                       9
% 2.14/1.00  merged_defs:                            8
% 2.14/1.00  merged_defs_ncl:                        0
% 2.14/1.00  bin_hyper_res:                          8
% 2.14/1.00  prep_cycles:                            4
% 2.14/1.00  pred_elim_time:                         0.042
% 2.14/1.00  splitting_time:                         0.
% 2.14/1.00  sem_filter_time:                        0.
% 2.14/1.00  monotx_time:                            0.001
% 2.14/1.00  subtype_inf_time:                       0.
% 2.14/1.00  
% 2.14/1.00  ------ Problem properties
% 2.14/1.00  
% 2.14/1.00  clauses:                                29
% 2.14/1.00  conjectures:                            17
% 2.14/1.00  epr:                                    18
% 2.14/1.00  horn:                                   23
% 2.14/1.00  ground:                                 17
% 2.14/1.00  unary:                                  16
% 2.14/1.00  binary:                                 2
% 2.14/1.00  lits:                                   89
% 2.14/1.00  lits_eq:                                6
% 2.14/1.00  fd_pure:                                0
% 2.14/1.00  fd_pseudo:                              0
% 2.14/1.00  fd_cond:                                0
% 2.14/1.00  fd_pseudo_cond:                         1
% 2.14/1.00  ac_symbols:                             0
% 2.14/1.00  
% 2.14/1.00  ------ Propositional Solver
% 2.14/1.00  
% 2.14/1.00  prop_solver_calls:                      27
% 2.14/1.00  prop_fast_solver_calls:                 1640
% 2.14/1.00  smt_solver_calls:                       0
% 2.14/1.00  smt_fast_solver_calls:                  0
% 2.14/1.00  prop_num_of_clauses:                    1079
% 2.14/1.00  prop_preprocess_simplified:             4590
% 2.14/1.00  prop_fo_subsumed:                       57
% 2.14/1.00  prop_solver_time:                       0.
% 2.14/1.00  smt_solver_time:                        0.
% 2.14/1.00  smt_fast_solver_time:                   0.
% 2.14/1.00  prop_fast_solver_time:                  0.
% 2.14/1.00  prop_unsat_core_time:                   0.
% 2.14/1.00  
% 2.14/1.00  ------ QBF
% 2.14/1.00  
% 2.14/1.00  qbf_q_res:                              0
% 2.14/1.00  qbf_num_tautologies:                    0
% 2.14/1.00  qbf_prep_cycles:                        0
% 2.14/1.00  
% 2.14/1.00  ------ BMC1
% 2.14/1.00  
% 2.14/1.00  bmc1_current_bound:                     -1
% 2.14/1.00  bmc1_last_solved_bound:                 -1
% 2.14/1.00  bmc1_unsat_core_size:                   -1
% 2.14/1.00  bmc1_unsat_core_parents_size:           -1
% 2.14/1.00  bmc1_merge_next_fun:                    0
% 2.14/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.14/1.00  
% 2.14/1.00  ------ Instantiation
% 2.14/1.00  
% 2.14/1.00  inst_num_of_clauses:                    306
% 2.14/1.00  inst_num_in_passive:                    6
% 2.14/1.00  inst_num_in_active:                     242
% 2.14/1.00  inst_num_in_unprocessed:                58
% 2.14/1.00  inst_num_of_loops:                      270
% 2.14/1.00  inst_num_of_learning_restarts:          0
% 2.14/1.00  inst_num_moves_active_passive:          25
% 2.14/1.00  inst_lit_activity:                      0
% 2.14/1.00  inst_lit_activity_moves:                0
% 2.14/1.00  inst_num_tautologies:                   0
% 2.14/1.00  inst_num_prop_implied:                  0
% 2.14/1.00  inst_num_existing_simplified:           0
% 2.14/1.00  inst_num_eq_res_simplified:             0
% 2.14/1.00  inst_num_child_elim:                    0
% 2.14/1.00  inst_num_of_dismatching_blockings:      19
% 2.14/1.00  inst_num_of_non_proper_insts:           407
% 2.14/1.00  inst_num_of_duplicates:                 0
% 2.14/1.00  inst_inst_num_from_inst_to_res:         0
% 2.14/1.00  inst_dismatching_checking_time:         0.
% 2.14/1.00  
% 2.14/1.00  ------ Resolution
% 2.14/1.00  
% 2.14/1.00  res_num_of_clauses:                     0
% 2.14/1.00  res_num_in_passive:                     0
% 2.14/1.00  res_num_in_active:                      0
% 2.14/1.00  res_num_of_loops:                       155
% 2.14/1.00  res_forward_subset_subsumed:            76
% 2.14/1.00  res_backward_subset_subsumed:           0
% 2.14/1.00  res_forward_subsumed:                   0
% 2.14/1.00  res_backward_subsumed:                  0
% 2.14/1.00  res_forward_subsumption_resolution:     1
% 2.14/1.00  res_backward_subsumption_resolution:    0
% 2.14/1.00  res_clause_to_clause_subsumption:       215
% 2.14/1.00  res_orphan_elimination:                 0
% 2.14/1.00  res_tautology_del:                      82
% 2.14/1.00  res_num_eq_res_simplified:              0
% 2.14/1.00  res_num_sel_changes:                    0
% 2.14/1.00  res_moves_from_active_to_pass:          0
% 2.14/1.00  
% 2.14/1.00  ------ Superposition
% 2.14/1.00  
% 2.14/1.00  sup_time_total:                         0.
% 2.14/1.00  sup_time_generating:                    0.
% 2.14/1.00  sup_time_sim_full:                      0.
% 2.14/1.00  sup_time_sim_immed:                     0.
% 2.14/1.00  
% 2.14/1.00  sup_num_of_clauses:                     58
% 2.14/1.00  sup_num_in_active:                      54
% 2.14/1.00  sup_num_in_passive:                     4
% 2.14/1.00  sup_num_of_loops:                       53
% 2.14/1.00  sup_fw_superposition:                   25
% 2.14/1.00  sup_bw_superposition:                   6
% 2.14/1.00  sup_immediate_simplified:               1
% 2.14/1.00  sup_given_eliminated:                   0
% 2.14/1.00  comparisons_done:                       0
% 2.14/1.00  comparisons_avoided:                    0
% 2.14/1.00  
% 2.14/1.00  ------ Simplifications
% 2.14/1.00  
% 2.14/1.00  
% 2.14/1.00  sim_fw_subset_subsumed:                 1
% 2.14/1.00  sim_bw_subset_subsumed:                 0
% 2.14/1.00  sim_fw_subsumed:                        0
% 2.14/1.00  sim_bw_subsumed:                        0
% 2.14/1.00  sim_fw_subsumption_res:                 0
% 2.14/1.00  sim_bw_subsumption_res:                 0
% 2.14/1.00  sim_tautology_del:                      2
% 2.14/1.00  sim_eq_tautology_del:                   1
% 2.14/1.00  sim_eq_res_simp:                        0
% 2.14/1.00  sim_fw_demodulated:                     0
% 2.14/1.00  sim_bw_demodulated:                     0
% 2.14/1.00  sim_light_normalised:                   3
% 2.14/1.00  sim_joinable_taut:                      0
% 2.14/1.00  sim_joinable_simp:                      0
% 2.14/1.00  sim_ac_normalised:                      0
% 2.14/1.00  sim_smt_subsumption:                    0
% 2.14/1.00  
%------------------------------------------------------------------------------
