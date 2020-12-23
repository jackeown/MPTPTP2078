%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:17 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 808 expanded)
%              Number of clauses        :   92 ( 138 expanded)
%              Number of leaves         :   23 ( 387 expanded)
%              Depth                    :   16
%              Number of atoms          : 1007 (13443 expanded)
%              Number of equality atoms :  207 ( 246 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   42 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_tmap_1(X1,X0,X4,X5)
                              & v5_pre_topc(X3,X2,X1) )
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                                 => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) ) ) ) ) ) ) ) ) ) ),
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
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_tmap_1(X1,X0,X4,X5)
                                & v5_pre_topc(X3,X2,X1) )
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                                   => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,X0,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,X0,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
          & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),sK9)
        & r2_hidden(sK9,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
        & m1_subset_1(sK9,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & r1_tmap_1(X1,X0,X4,X5)
          & v5_pre_topc(X3,X2,X1)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
            & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),sK8)))
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & r1_tmap_1(X1,X0,X4,sK8)
        & v5_pre_topc(X3,X2,X1)
        & m1_subset_1(sK8,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                  & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & r1_tmap_1(X1,X0,X4,X5)
              & v5_pre_topc(X3,X2,X1)
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,sK7),X6)
                & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & r1_tmap_1(X1,X0,sK7,X5)
            & v5_pre_topc(X3,X2,X1)
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK7,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                      & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & r1_tmap_1(X1,X0,X4,X5)
                  & v5_pre_topc(X3,X2,X1)
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),sK6,X4),X6)
                    & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK6,k6_domain_1(u1_struct_0(X1),X5)))
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & r1_tmap_1(X1,X0,X4,X5)
                & v5_pre_topc(sK6,X2,X1)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                          & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & r1_tmap_1(X1,X0,X4,X5)
                      & v5_pre_topc(X3,X2,X1)
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(sK5,X0,k1_partfun1(u1_struct_0(sK5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                        & r2_hidden(X6,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                        & m1_subset_1(X6,u1_struct_0(sK5)) )
                    & r1_tmap_1(X1,X0,X4,X5)
                    & v5_pre_topc(X3,sK5,X1)
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,X0,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(X0),X3,X4),X6)
                            & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK4),X3,k6_domain_1(u1_struct_0(sK4),X5)))
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & r1_tmap_1(sK4,X0,X4,X5)
                        & v5_pre_topc(X3,X2,sK4)
                        & m1_subset_1(X5,u1_struct_0(sK4)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK4))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK4))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                                & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & r1_tmap_1(X1,X0,X4,X5)
                            & v5_pre_topc(X3,X2,X1)
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
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
                              ( ~ r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK3),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,sK3,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ~ r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9)
    & r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8)))
    & m1_subset_1(sK9,u1_struct_0(sK5))
    & r1_tmap_1(sK4,sK3,sK7,sK8)
    & v5_pre_topc(sK6,sK5,sK4)
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f33,f53,f52,f51,f50,f49,f48,f47])).

fof(f92,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f70,f59])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1)
                | ~ r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f86,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f105,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f95,plain,(
    m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f54])).

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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_tmap_1(X2,X0,X4,X6)
                                  & r1_tmap_1(X1,X2,X3,X5)
                                  & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6 )
                               => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,X6)
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f97,plain,(
    ~ r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f54])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2))
                    & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    v5_pre_topc(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f94,plain,(
    r1_tmap_1(sK4,sK3,sK7,sK8) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1949,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1957,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3510,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK8) = k2_tarski(sK8,sK8)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1949,c_1957])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1955,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,k1_connsp_2(X1,X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1956,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1967,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5698,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,k1_connsp_2(X1,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1956,c_1967])).

cnf(c_7221,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1955,c_5698])).

cnf(c_7421,plain,
    ( v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1949,c_7221])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_45,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_46,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_47,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_8572,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7421,c_45,c_46,c_47])).

cnf(c_8577,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK8) = k2_tarski(sK8,sK8) ),
    inference(superposition,[status(thm)],[c_3510,c_8572])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1945,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1959,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4101,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k10_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1945,c_1959])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1952,plain,
    ( r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4888,plain,
    ( r2_hidden(sK9,k10_relat_1(sK6,k6_domain_1(u1_struct_0(sK4),sK8))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4101,c_1952])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1962,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5644,plain,
    ( r2_hidden(k1_funct_1(sK6,sK9),k6_domain_1(u1_struct_0(sK4),sK8)) = iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4888,c_1962])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_51,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_53,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2336,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2337,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_6546,plain,
    ( r2_hidden(k1_funct_1(sK6,sK9),k6_domain_1(u1_struct_0(sK4),sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5644,c_51,c_53,c_2337])).

cnf(c_8987,plain,
    ( r2_hidden(k1_funct_1(sK6,sK9),k2_tarski(sK8,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8577,c_6546])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1968,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10546,plain,
    ( k1_funct_1(sK6,sK9) = sK8 ),
    inference(superposition,[status(thm)],[c_8987,c_1968])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1951,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1958,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7449,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k1_funct_1(sK6,X0)
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1945,c_1958])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_48,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_49,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_50,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_52,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7420,plain,
    ( v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1951,c_7221])).

cnf(c_8897,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k1_funct_1(sK6,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7449,c_48,c_49,c_50,c_51,c_52,c_7420])).

cnf(c_8905,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9) = k1_funct_1(sK6,sK9) ),
    inference(superposition,[status(thm)],[c_1951,c_8897])).

cnf(c_20,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1))
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1954,plain,
    ( r1_tmap_1(X0,X1,X2,X3) != iProver_top
    | r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != iProver_top
    | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3) = iProver_top
    | v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1953,plain,
    ( r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5636,plain,
    ( r1_tmap_1(sK4,sK3,sK7,k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9)) != iProver_top
    | r1_tmap_1(sK5,sK4,sK6,sK9) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1953])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_42,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_44,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_54,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_55,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_56,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_60,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,negated_conjecture,
    ( v5_pre_topc(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_729,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | sK6 != X2
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_730,plain,
    ( r1_tmap_1(sK5,sK4,sK6,X0)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | v2_struct_0(sK4)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK5)
    | ~ v1_funct_1(sK6) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_734,plain,
    ( r1_tmap_1(sK5,sK4,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30])).

cnf(c_2330,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_2331,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2330])).

cnf(c_6282,plain,
    ( r1_tmap_1(sK4,sK3,sK7,k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9)) != iProver_top
    | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5636,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_60,c_2331])).

cnf(c_8909,plain,
    ( r1_tmap_1(sK4,sK3,sK7,k1_funct_1(sK6,sK9)) != iProver_top
    | m1_subset_1(k1_funct_1(sK6,sK9),u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8905,c_6282])).

cnf(c_10755,plain,
    ( r1_tmap_1(sK4,sK3,sK7,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10546,c_8909])).

cnf(c_24,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,sK7,sK8) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_59,plain,
    ( r1_tmap_1(sK4,sK3,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_57,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10755,c_59,c_57])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.66/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.00  
% 3.66/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/1.00  
% 3.66/1.00  ------  iProver source info
% 3.66/1.00  
% 3.66/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.66/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/1.00  git: non_committed_changes: false
% 3.66/1.00  git: last_make_outside_of_git: false
% 3.66/1.00  
% 3.66/1.00  ------ 
% 3.66/1.00  
% 3.66/1.00  ------ Input Options
% 3.66/1.00  
% 3.66/1.00  --out_options                           all
% 3.66/1.00  --tptp_safe_out                         true
% 3.66/1.00  --problem_path                          ""
% 3.66/1.00  --include_path                          ""
% 3.66/1.00  --clausifier                            res/vclausify_rel
% 3.66/1.00  --clausifier_options                    --mode clausify
% 3.66/1.00  --stdin                                 false
% 3.66/1.00  --stats_out                             all
% 3.66/1.00  
% 3.66/1.00  ------ General Options
% 3.66/1.00  
% 3.66/1.00  --fof                                   false
% 3.66/1.00  --time_out_real                         305.
% 3.66/1.00  --time_out_virtual                      -1.
% 3.66/1.00  --symbol_type_check                     false
% 3.66/1.00  --clausify_out                          false
% 3.66/1.00  --sig_cnt_out                           false
% 3.66/1.00  --trig_cnt_out                          false
% 3.66/1.00  --trig_cnt_out_tolerance                1.
% 3.66/1.00  --trig_cnt_out_sk_spl                   false
% 3.66/1.00  --abstr_cl_out                          false
% 3.66/1.00  
% 3.66/1.00  ------ Global Options
% 3.66/1.00  
% 3.66/1.00  --schedule                              default
% 3.66/1.00  --add_important_lit                     false
% 3.66/1.00  --prop_solver_per_cl                    1000
% 3.66/1.00  --min_unsat_core                        false
% 3.66/1.00  --soft_assumptions                      false
% 3.66/1.00  --soft_lemma_size                       3
% 3.66/1.00  --prop_impl_unit_size                   0
% 3.66/1.00  --prop_impl_unit                        []
% 3.66/1.00  --share_sel_clauses                     true
% 3.66/1.00  --reset_solvers                         false
% 3.66/1.00  --bc_imp_inh                            [conj_cone]
% 3.66/1.00  --conj_cone_tolerance                   3.
% 3.66/1.00  --extra_neg_conj                        none
% 3.66/1.00  --large_theory_mode                     true
% 3.66/1.00  --prolific_symb_bound                   200
% 3.66/1.00  --lt_threshold                          2000
% 3.66/1.00  --clause_weak_htbl                      true
% 3.66/1.00  --gc_record_bc_elim                     false
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing Options
% 3.66/1.00  
% 3.66/1.00  --preprocessing_flag                    true
% 3.66/1.00  --time_out_prep_mult                    0.1
% 3.66/1.00  --splitting_mode                        input
% 3.66/1.00  --splitting_grd                         true
% 3.66/1.00  --splitting_cvd                         false
% 3.66/1.00  --splitting_cvd_svl                     false
% 3.66/1.00  --splitting_nvd                         32
% 3.66/1.00  --sub_typing                            true
% 3.66/1.00  --prep_gs_sim                           true
% 3.66/1.00  --prep_unflatten                        true
% 3.66/1.00  --prep_res_sim                          true
% 3.66/1.00  --prep_upred                            true
% 3.66/1.00  --prep_sem_filter                       exhaustive
% 3.66/1.00  --prep_sem_filter_out                   false
% 3.66/1.00  --pred_elim                             true
% 3.66/1.00  --res_sim_input                         true
% 3.66/1.00  --eq_ax_congr_red                       true
% 3.66/1.00  --pure_diseq_elim                       true
% 3.66/1.00  --brand_transform                       false
% 3.66/1.00  --non_eq_to_eq                          false
% 3.66/1.00  --prep_def_merge                        true
% 3.66/1.00  --prep_def_merge_prop_impl              false
% 3.66/1.00  --prep_def_merge_mbd                    true
% 3.66/1.00  --prep_def_merge_tr_red                 false
% 3.66/1.00  --prep_def_merge_tr_cl                  false
% 3.66/1.00  --smt_preprocessing                     true
% 3.66/1.00  --smt_ac_axioms                         fast
% 3.66/1.00  --preprocessed_out                      false
% 3.66/1.00  --preprocessed_stats                    false
% 3.66/1.00  
% 3.66/1.00  ------ Abstraction refinement Options
% 3.66/1.00  
% 3.66/1.00  --abstr_ref                             []
% 3.66/1.00  --abstr_ref_prep                        false
% 3.66/1.00  --abstr_ref_until_sat                   false
% 3.66/1.00  --abstr_ref_sig_restrict                funpre
% 3.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.66/1.00  --abstr_ref_under                       []
% 3.66/1.00  
% 3.66/1.00  ------ SAT Options
% 3.66/1.00  
% 3.66/1.00  --sat_mode                              false
% 3.66/1.00  --sat_fm_restart_options                ""
% 3.66/1.00  --sat_gr_def                            false
% 3.66/1.00  --sat_epr_types                         true
% 3.66/1.00  --sat_non_cyclic_types                  false
% 3.66/1.00  --sat_finite_models                     false
% 3.66/1.00  --sat_fm_lemmas                         false
% 3.66/1.00  --sat_fm_prep                           false
% 3.66/1.00  --sat_fm_uc_incr                        true
% 3.66/1.00  --sat_out_model                         small
% 3.66/1.00  --sat_out_clauses                       false
% 3.66/1.00  
% 3.66/1.00  ------ QBF Options
% 3.66/1.00  
% 3.66/1.00  --qbf_mode                              false
% 3.66/1.00  --qbf_elim_univ                         false
% 3.66/1.00  --qbf_dom_inst                          none
% 3.66/1.00  --qbf_dom_pre_inst                      false
% 3.66/1.00  --qbf_sk_in                             false
% 3.66/1.00  --qbf_pred_elim                         true
% 3.66/1.00  --qbf_split                             512
% 3.66/1.00  
% 3.66/1.00  ------ BMC1 Options
% 3.66/1.00  
% 3.66/1.00  --bmc1_incremental                      false
% 3.66/1.00  --bmc1_axioms                           reachable_all
% 3.66/1.00  --bmc1_min_bound                        0
% 3.66/1.00  --bmc1_max_bound                        -1
% 3.66/1.00  --bmc1_max_bound_default                -1
% 3.66/1.00  --bmc1_symbol_reachability              true
% 3.66/1.00  --bmc1_property_lemmas                  false
% 3.66/1.00  --bmc1_k_induction                      false
% 3.66/1.00  --bmc1_non_equiv_states                 false
% 3.66/1.00  --bmc1_deadlock                         false
% 3.66/1.00  --bmc1_ucm                              false
% 3.66/1.00  --bmc1_add_unsat_core                   none
% 3.66/1.00  --bmc1_unsat_core_children              false
% 3.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.66/1.00  --bmc1_out_stat                         full
% 3.66/1.00  --bmc1_ground_init                      false
% 3.66/1.00  --bmc1_pre_inst_next_state              false
% 3.66/1.00  --bmc1_pre_inst_state                   false
% 3.66/1.00  --bmc1_pre_inst_reach_state             false
% 3.66/1.00  --bmc1_out_unsat_core                   false
% 3.66/1.00  --bmc1_aig_witness_out                  false
% 3.66/1.00  --bmc1_verbose                          false
% 3.66/1.00  --bmc1_dump_clauses_tptp                false
% 3.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.66/1.00  --bmc1_dump_file                        -
% 3.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.66/1.00  --bmc1_ucm_extend_mode                  1
% 3.66/1.00  --bmc1_ucm_init_mode                    2
% 3.66/1.00  --bmc1_ucm_cone_mode                    none
% 3.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.66/1.00  --bmc1_ucm_relax_model                  4
% 3.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.66/1.00  --bmc1_ucm_layered_model                none
% 3.66/1.00  --bmc1_ucm_max_lemma_size               10
% 3.66/1.00  
% 3.66/1.00  ------ AIG Options
% 3.66/1.00  
% 3.66/1.00  --aig_mode                              false
% 3.66/1.00  
% 3.66/1.00  ------ Instantiation Options
% 3.66/1.00  
% 3.66/1.00  --instantiation_flag                    true
% 3.66/1.00  --inst_sos_flag                         false
% 3.66/1.00  --inst_sos_phase                        true
% 3.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.66/1.00  --inst_lit_sel_side                     num_symb
% 3.66/1.00  --inst_solver_per_active                1400
% 3.66/1.00  --inst_solver_calls_frac                1.
% 3.66/1.00  --inst_passive_queue_type               priority_queues
% 3.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.66/1.00  --inst_passive_queues_freq              [25;2]
% 3.66/1.00  --inst_dismatching                      true
% 3.66/1.00  --inst_eager_unprocessed_to_passive     true
% 3.66/1.00  --inst_prop_sim_given                   true
% 3.66/1.00  --inst_prop_sim_new                     false
% 3.66/1.00  --inst_subs_new                         false
% 3.66/1.00  --inst_eq_res_simp                      false
% 3.66/1.00  --inst_subs_given                       false
% 3.66/1.00  --inst_orphan_elimination               true
% 3.66/1.00  --inst_learning_loop_flag               true
% 3.66/1.00  --inst_learning_start                   3000
% 3.66/1.00  --inst_learning_factor                  2
% 3.66/1.00  --inst_start_prop_sim_after_learn       3
% 3.66/1.00  --inst_sel_renew                        solver
% 3.66/1.00  --inst_lit_activity_flag                true
% 3.66/1.00  --inst_restr_to_given                   false
% 3.66/1.00  --inst_activity_threshold               500
% 3.66/1.00  --inst_out_proof                        true
% 3.66/1.00  
% 3.66/1.00  ------ Resolution Options
% 3.66/1.00  
% 3.66/1.00  --resolution_flag                       true
% 3.66/1.00  --res_lit_sel                           adaptive
% 3.66/1.00  --res_lit_sel_side                      none
% 3.66/1.00  --res_ordering                          kbo
% 3.66/1.00  --res_to_prop_solver                    active
% 3.66/1.00  --res_prop_simpl_new                    false
% 3.66/1.00  --res_prop_simpl_given                  true
% 3.66/1.00  --res_passive_queue_type                priority_queues
% 3.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.66/1.00  --res_passive_queues_freq               [15;5]
% 3.66/1.00  --res_forward_subs                      full
% 3.66/1.00  --res_backward_subs                     full
% 3.66/1.00  --res_forward_subs_resolution           true
% 3.66/1.00  --res_backward_subs_resolution          true
% 3.66/1.00  --res_orphan_elimination                true
% 3.66/1.00  --res_time_limit                        2.
% 3.66/1.00  --res_out_proof                         true
% 3.66/1.00  
% 3.66/1.00  ------ Superposition Options
% 3.66/1.00  
% 3.66/1.00  --superposition_flag                    true
% 3.66/1.00  --sup_passive_queue_type                priority_queues
% 3.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.66/1.00  --demod_completeness_check              fast
% 3.66/1.00  --demod_use_ground                      true
% 3.66/1.00  --sup_to_prop_solver                    passive
% 3.66/1.00  --sup_prop_simpl_new                    true
% 3.66/1.00  --sup_prop_simpl_given                  true
% 3.66/1.00  --sup_fun_splitting                     false
% 3.66/1.00  --sup_smt_interval                      50000
% 3.66/1.00  
% 3.66/1.00  ------ Superposition Simplification Setup
% 3.66/1.00  
% 3.66/1.00  --sup_indices_passive                   []
% 3.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_full_bw                           [BwDemod]
% 3.66/1.00  --sup_immed_triv                        [TrivRules]
% 3.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_immed_bw_main                     []
% 3.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.00  
% 3.66/1.00  ------ Combination Options
% 3.66/1.00  
% 3.66/1.00  --comb_res_mult                         3
% 3.66/1.00  --comb_sup_mult                         2
% 3.66/1.00  --comb_inst_mult                        10
% 3.66/1.00  
% 3.66/1.00  ------ Debug Options
% 3.66/1.00  
% 3.66/1.00  --dbg_backtrace                         false
% 3.66/1.00  --dbg_dump_prop_clauses                 false
% 3.66/1.00  --dbg_dump_prop_clauses_file            -
% 3.66/1.00  --dbg_out_stat                          false
% 3.66/1.00  ------ Parsing...
% 3.66/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/1.00  ------ Proving...
% 3.66/1.00  ------ Problem Properties 
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  clauses                                 41
% 3.66/1.00  conjectures                             20
% 3.66/1.00  EPR                                     12
% 3.66/1.00  Horn                                    31
% 3.66/1.00  unary                                   21
% 3.66/1.00  binary                                  4
% 3.66/1.00  lits                                    130
% 3.66/1.00  lits eq                                 11
% 3.66/1.00  fd_pure                                 0
% 3.66/1.00  fd_pseudo                               0
% 3.66/1.00  fd_cond                                 0
% 3.66/1.00  fd_pseudo_cond                          5
% 3.66/1.00  AC symbols                              0
% 3.66/1.00  
% 3.66/1.00  ------ Schedule dynamic 5 is on 
% 3.66/1.00  
% 3.66/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  ------ 
% 3.66/1.00  Current options:
% 3.66/1.00  ------ 
% 3.66/1.00  
% 3.66/1.00  ------ Input Options
% 3.66/1.00  
% 3.66/1.00  --out_options                           all
% 3.66/1.00  --tptp_safe_out                         true
% 3.66/1.00  --problem_path                          ""
% 3.66/1.00  --include_path                          ""
% 3.66/1.00  --clausifier                            res/vclausify_rel
% 3.66/1.00  --clausifier_options                    --mode clausify
% 3.66/1.00  --stdin                                 false
% 3.66/1.00  --stats_out                             all
% 3.66/1.00  
% 3.66/1.00  ------ General Options
% 3.66/1.00  
% 3.66/1.00  --fof                                   false
% 3.66/1.00  --time_out_real                         305.
% 3.66/1.00  --time_out_virtual                      -1.
% 3.66/1.00  --symbol_type_check                     false
% 3.66/1.00  --clausify_out                          false
% 3.66/1.00  --sig_cnt_out                           false
% 3.66/1.00  --trig_cnt_out                          false
% 3.66/1.00  --trig_cnt_out_tolerance                1.
% 3.66/1.00  --trig_cnt_out_sk_spl                   false
% 3.66/1.00  --abstr_cl_out                          false
% 3.66/1.00  
% 3.66/1.00  ------ Global Options
% 3.66/1.00  
% 3.66/1.00  --schedule                              default
% 3.66/1.00  --add_important_lit                     false
% 3.66/1.00  --prop_solver_per_cl                    1000
% 3.66/1.00  --min_unsat_core                        false
% 3.66/1.00  --soft_assumptions                      false
% 3.66/1.00  --soft_lemma_size                       3
% 3.66/1.00  --prop_impl_unit_size                   0
% 3.66/1.00  --prop_impl_unit                        []
% 3.66/1.00  --share_sel_clauses                     true
% 3.66/1.00  --reset_solvers                         false
% 3.66/1.00  --bc_imp_inh                            [conj_cone]
% 3.66/1.00  --conj_cone_tolerance                   3.
% 3.66/1.00  --extra_neg_conj                        none
% 3.66/1.00  --large_theory_mode                     true
% 3.66/1.00  --prolific_symb_bound                   200
% 3.66/1.00  --lt_threshold                          2000
% 3.66/1.00  --clause_weak_htbl                      true
% 3.66/1.00  --gc_record_bc_elim                     false
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing Options
% 3.66/1.00  
% 3.66/1.00  --preprocessing_flag                    true
% 3.66/1.00  --time_out_prep_mult                    0.1
% 3.66/1.00  --splitting_mode                        input
% 3.66/1.00  --splitting_grd                         true
% 3.66/1.00  --splitting_cvd                         false
% 3.66/1.00  --splitting_cvd_svl                     false
% 3.66/1.00  --splitting_nvd                         32
% 3.66/1.00  --sub_typing                            true
% 3.66/1.00  --prep_gs_sim                           true
% 3.66/1.00  --prep_unflatten                        true
% 3.66/1.00  --prep_res_sim                          true
% 3.66/1.00  --prep_upred                            true
% 3.66/1.00  --prep_sem_filter                       exhaustive
% 3.66/1.00  --prep_sem_filter_out                   false
% 3.66/1.00  --pred_elim                             true
% 3.66/1.00  --res_sim_input                         true
% 3.66/1.00  --eq_ax_congr_red                       true
% 3.66/1.00  --pure_diseq_elim                       true
% 3.66/1.00  --brand_transform                       false
% 3.66/1.00  --non_eq_to_eq                          false
% 3.66/1.00  --prep_def_merge                        true
% 3.66/1.00  --prep_def_merge_prop_impl              false
% 3.66/1.00  --prep_def_merge_mbd                    true
% 3.66/1.00  --prep_def_merge_tr_red                 false
% 3.66/1.00  --prep_def_merge_tr_cl                  false
% 3.66/1.00  --smt_preprocessing                     true
% 3.66/1.00  --smt_ac_axioms                         fast
% 3.66/1.00  --preprocessed_out                      false
% 3.66/1.00  --preprocessed_stats                    false
% 3.66/1.00  
% 3.66/1.00  ------ Abstraction refinement Options
% 3.66/1.00  
% 3.66/1.00  --abstr_ref                             []
% 3.66/1.00  --abstr_ref_prep                        false
% 3.66/1.00  --abstr_ref_until_sat                   false
% 3.66/1.00  --abstr_ref_sig_restrict                funpre
% 3.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.66/1.00  --abstr_ref_under                       []
% 3.66/1.00  
% 3.66/1.00  ------ SAT Options
% 3.66/1.00  
% 3.66/1.00  --sat_mode                              false
% 3.66/1.00  --sat_fm_restart_options                ""
% 3.66/1.00  --sat_gr_def                            false
% 3.66/1.00  --sat_epr_types                         true
% 3.66/1.00  --sat_non_cyclic_types                  false
% 3.66/1.00  --sat_finite_models                     false
% 3.66/1.00  --sat_fm_lemmas                         false
% 3.66/1.00  --sat_fm_prep                           false
% 3.66/1.00  --sat_fm_uc_incr                        true
% 3.66/1.00  --sat_out_model                         small
% 3.66/1.00  --sat_out_clauses                       false
% 3.66/1.00  
% 3.66/1.00  ------ QBF Options
% 3.66/1.00  
% 3.66/1.00  --qbf_mode                              false
% 3.66/1.00  --qbf_elim_univ                         false
% 3.66/1.00  --qbf_dom_inst                          none
% 3.66/1.00  --qbf_dom_pre_inst                      false
% 3.66/1.00  --qbf_sk_in                             false
% 3.66/1.00  --qbf_pred_elim                         true
% 3.66/1.00  --qbf_split                             512
% 3.66/1.00  
% 3.66/1.00  ------ BMC1 Options
% 3.66/1.00  
% 3.66/1.00  --bmc1_incremental                      false
% 3.66/1.00  --bmc1_axioms                           reachable_all
% 3.66/1.00  --bmc1_min_bound                        0
% 3.66/1.00  --bmc1_max_bound                        -1
% 3.66/1.00  --bmc1_max_bound_default                -1
% 3.66/1.00  --bmc1_symbol_reachability              true
% 3.66/1.00  --bmc1_property_lemmas                  false
% 3.66/1.00  --bmc1_k_induction                      false
% 3.66/1.00  --bmc1_non_equiv_states                 false
% 3.66/1.00  --bmc1_deadlock                         false
% 3.66/1.00  --bmc1_ucm                              false
% 3.66/1.00  --bmc1_add_unsat_core                   none
% 3.66/1.00  --bmc1_unsat_core_children              false
% 3.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.66/1.00  --bmc1_out_stat                         full
% 3.66/1.00  --bmc1_ground_init                      false
% 3.66/1.00  --bmc1_pre_inst_next_state              false
% 3.66/1.00  --bmc1_pre_inst_state                   false
% 3.66/1.00  --bmc1_pre_inst_reach_state             false
% 3.66/1.00  --bmc1_out_unsat_core                   false
% 3.66/1.00  --bmc1_aig_witness_out                  false
% 3.66/1.00  --bmc1_verbose                          false
% 3.66/1.00  --bmc1_dump_clauses_tptp                false
% 3.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.66/1.00  --bmc1_dump_file                        -
% 3.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.66/1.00  --bmc1_ucm_extend_mode                  1
% 3.66/1.00  --bmc1_ucm_init_mode                    2
% 3.66/1.00  --bmc1_ucm_cone_mode                    none
% 3.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.66/1.00  --bmc1_ucm_relax_model                  4
% 3.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.66/1.00  --bmc1_ucm_layered_model                none
% 3.66/1.00  --bmc1_ucm_max_lemma_size               10
% 3.66/1.00  
% 3.66/1.00  ------ AIG Options
% 3.66/1.00  
% 3.66/1.00  --aig_mode                              false
% 3.66/1.00  
% 3.66/1.00  ------ Instantiation Options
% 3.66/1.00  
% 3.66/1.00  --instantiation_flag                    true
% 3.66/1.00  --inst_sos_flag                         false
% 3.66/1.00  --inst_sos_phase                        true
% 3.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.66/1.00  --inst_lit_sel_side                     none
% 3.66/1.00  --inst_solver_per_active                1400
% 3.66/1.00  --inst_solver_calls_frac                1.
% 3.66/1.00  --inst_passive_queue_type               priority_queues
% 3.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.66/1.00  --inst_passive_queues_freq              [25;2]
% 3.66/1.00  --inst_dismatching                      true
% 3.66/1.00  --inst_eager_unprocessed_to_passive     true
% 3.66/1.00  --inst_prop_sim_given                   true
% 3.66/1.00  --inst_prop_sim_new                     false
% 3.66/1.00  --inst_subs_new                         false
% 3.66/1.00  --inst_eq_res_simp                      false
% 3.66/1.00  --inst_subs_given                       false
% 3.66/1.00  --inst_orphan_elimination               true
% 3.66/1.00  --inst_learning_loop_flag               true
% 3.66/1.00  --inst_learning_start                   3000
% 3.66/1.00  --inst_learning_factor                  2
% 3.66/1.00  --inst_start_prop_sim_after_learn       3
% 3.66/1.00  --inst_sel_renew                        solver
% 3.66/1.00  --inst_lit_activity_flag                true
% 3.66/1.00  --inst_restr_to_given                   false
% 3.66/1.00  --inst_activity_threshold               500
% 3.66/1.00  --inst_out_proof                        true
% 3.66/1.00  
% 3.66/1.00  ------ Resolution Options
% 3.66/1.00  
% 3.66/1.00  --resolution_flag                       false
% 3.66/1.00  --res_lit_sel                           adaptive
% 3.66/1.00  --res_lit_sel_side                      none
% 3.66/1.00  --res_ordering                          kbo
% 3.66/1.00  --res_to_prop_solver                    active
% 3.66/1.00  --res_prop_simpl_new                    false
% 3.66/1.00  --res_prop_simpl_given                  true
% 3.66/1.00  --res_passive_queue_type                priority_queues
% 3.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.66/1.00  --res_passive_queues_freq               [15;5]
% 3.66/1.00  --res_forward_subs                      full
% 3.66/1.00  --res_backward_subs                     full
% 3.66/1.00  --res_forward_subs_resolution           true
% 3.66/1.00  --res_backward_subs_resolution          true
% 3.66/1.00  --res_orphan_elimination                true
% 3.66/1.00  --res_time_limit                        2.
% 3.66/1.00  --res_out_proof                         true
% 3.66/1.00  
% 3.66/1.00  ------ Superposition Options
% 3.66/1.00  
% 3.66/1.00  --superposition_flag                    true
% 3.66/1.00  --sup_passive_queue_type                priority_queues
% 3.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.66/1.00  --demod_completeness_check              fast
% 3.66/1.00  --demod_use_ground                      true
% 3.66/1.00  --sup_to_prop_solver                    passive
% 3.66/1.00  --sup_prop_simpl_new                    true
% 3.66/1.00  --sup_prop_simpl_given                  true
% 3.66/1.00  --sup_fun_splitting                     false
% 3.66/1.00  --sup_smt_interval                      50000
% 3.66/1.00  
% 3.66/1.00  ------ Superposition Simplification Setup
% 3.66/1.00  
% 3.66/1.00  --sup_indices_passive                   []
% 3.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_full_bw                           [BwDemod]
% 3.66/1.00  --sup_immed_triv                        [TrivRules]
% 3.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_immed_bw_main                     []
% 3.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.66/1.00  
% 3.66/1.00  ------ Combination Options
% 3.66/1.00  
% 3.66/1.00  --comb_res_mult                         3
% 3.66/1.00  --comb_sup_mult                         2
% 3.66/1.00  --comb_inst_mult                        10
% 3.66/1.00  
% 3.66/1.00  ------ Debug Options
% 3.66/1.00  
% 3.66/1.00  --dbg_backtrace                         false
% 3.66/1.00  --dbg_dump_prop_clauses                 false
% 3.66/1.00  --dbg_dump_prop_clauses_file            -
% 3.66/1.00  --dbg_out_stat                          false
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  ------ Proving...
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  % SZS status Theorem for theBenchmark.p
% 3.66/1.00  
% 3.66/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/1.00  
% 3.66/1.00  fof(f13,conjecture,(
% 3.66/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f14,negated_conjecture,(
% 3.66/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 3.66/1.00    inference(negated_conjecture,[],[f13])).
% 3.66/1.00  
% 3.66/1.00  fof(f32,plain,(
% 3.66/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : ((~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))) & m1_subset_1(X6,u1_struct_0(X2))) & (r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1))) & m1_subset_1(X5,u1_struct_0(X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f14])).
% 3.66/1.00  
% 3.66/1.00  fof(f33,plain,(
% 3.66/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.66/1.00    inference(flattening,[],[f32])).
% 3.66/1.00  
% 3.66/1.00  fof(f53,plain,(
% 3.66/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),sK9) & r2_hidden(sK9,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(sK9,u1_struct_0(X2)))) )),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f52,plain,(
% 3.66/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),sK8))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,sK8) & v5_pre_topc(X3,X2,X1) & m1_subset_1(sK8,u1_struct_0(X1)))) )),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f51,plain,(
% 3.66/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,sK7),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,sK7,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK7,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK7))) )),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f50,plain,(
% 3.66/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),sK6,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK6,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(sK6,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f49,plain,(
% 3.66/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,X0,k1_partfun1(u1_struct_0(sK5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(sK5))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,sK5,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f48,plain,(
% 3.66/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK4),X3,k6_domain_1(u1_struct_0(sK4),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(sK4,X0,X4,X5) & v5_pre_topc(X3,X2,sK4) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK4)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK4)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f47,plain,(
% 3.66/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK3),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,sK3,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f54,plain,(
% 3.66/1.00    ((((((~r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) & r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) & m1_subset_1(sK9,u1_struct_0(sK5))) & r1_tmap_1(sK4,sK3,sK7,sK8) & v5_pre_topc(sK6,sK5,sK4) & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f33,f53,f52,f51,f50,f49,f48,f47])).
% 3.66/1.00  
% 3.66/1.00  fof(f92,plain,(
% 3.66/1.00    m1_subset_1(sK8,u1_struct_0(sK4))),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f8,axiom,(
% 3.66/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f22,plain,(
% 3.66/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f8])).
% 3.66/1.00  
% 3.66/1.00  fof(f23,plain,(
% 3.66/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.66/1.00    inference(flattening,[],[f22])).
% 3.66/1.00  
% 3.66/1.00  fof(f70,plain,(
% 3.66/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f23])).
% 3.66/1.00  
% 3.66/1.00  fof(f2,axiom,(
% 3.66/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f59,plain,(
% 3.66/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f2])).
% 3.66/1.00  
% 3.66/1.00  fof(f102,plain,(
% 3.66/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.66/1.00    inference(definition_unfolding,[],[f70,f59])).
% 3.66/1.00  
% 3.66/1.00  fof(f10,axiom,(
% 3.66/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f26,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f10])).
% 3.66/1.00  
% 3.66/1.00  fof(f27,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/1.00    inference(flattening,[],[f26])).
% 3.66/1.00  
% 3.66/1.00  fof(f72,plain,(
% 3.66/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f27])).
% 3.66/1.00  
% 3.66/1.00  fof(f9,axiom,(
% 3.66/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f24,plain,(
% 3.66/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f9])).
% 3.66/1.00  
% 3.66/1.00  fof(f25,plain,(
% 3.66/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/1.00    inference(flattening,[],[f24])).
% 3.66/1.00  
% 3.66/1.00  fof(f71,plain,(
% 3.66/1.00    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f25])).
% 3.66/1.00  
% 3.66/1.00  fof(f3,axiom,(
% 3.66/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f15,plain,(
% 3.66/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.66/1.00    inference(ennf_transformation,[],[f3])).
% 3.66/1.00  
% 3.66/1.00  fof(f60,plain,(
% 3.66/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f15])).
% 3.66/1.00  
% 3.66/1.00  fof(f80,plain,(
% 3.66/1.00    ~v2_struct_0(sK4)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f81,plain,(
% 3.66/1.00    v2_pre_topc(sK4)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f82,plain,(
% 3.66/1.00    l1_pre_topc(sK4)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f88,plain,(
% 3.66/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f6,axiom,(
% 3.66/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f19,plain,(
% 3.66/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.00    inference(ennf_transformation,[],[f6])).
% 3.66/1.00  
% 3.66/1.00  fof(f68,plain,(
% 3.66/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.00    inference(cnf_transformation,[],[f19])).
% 3.66/1.00  
% 3.66/1.00  fof(f96,plain,(
% 3.66/1.00    r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8)))),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f4,axiom,(
% 3.66/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f16,plain,(
% 3.66/1.00    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f4])).
% 3.66/1.00  
% 3.66/1.00  fof(f17,plain,(
% 3.66/1.00    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.00    inference(flattening,[],[f16])).
% 3.66/1.00  
% 3.66/1.00  fof(f38,plain,(
% 3.66/1.00    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.00    inference(nnf_transformation,[],[f17])).
% 3.66/1.00  
% 3.66/1.00  fof(f39,plain,(
% 3.66/1.00    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.00    inference(flattening,[],[f38])).
% 3.66/1.00  
% 3.66/1.00  fof(f40,plain,(
% 3.66/1.00    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.00    inference(rectify,[],[f39])).
% 3.66/1.00  
% 3.66/1.00  fof(f41,plain,(
% 3.66/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f42,plain,(
% 3.66/1.00    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 3.66/1.00  
% 3.66/1.00  fof(f62,plain,(
% 3.66/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f42])).
% 3.66/1.00  
% 3.66/1.00  fof(f107,plain,(
% 3.66/1.00    ( ! [X4,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.00    inference(equality_resolution,[],[f62])).
% 3.66/1.00  
% 3.66/1.00  fof(f86,plain,(
% 3.66/1.00    v1_funct_1(sK6)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f5,axiom,(
% 3.66/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f18,plain,(
% 3.66/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.00    inference(ennf_transformation,[],[f5])).
% 3.66/1.00  
% 3.66/1.00  fof(f67,plain,(
% 3.66/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.00    inference(cnf_transformation,[],[f18])).
% 3.66/1.00  
% 3.66/1.00  fof(f1,axiom,(
% 3.66/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f34,plain,(
% 3.66/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.66/1.00    inference(nnf_transformation,[],[f1])).
% 3.66/1.00  
% 3.66/1.00  fof(f35,plain,(
% 3.66/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.66/1.00    inference(rectify,[],[f34])).
% 3.66/1.00  
% 3.66/1.00  fof(f36,plain,(
% 3.66/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f37,plain,(
% 3.66/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.66/1.00  
% 3.66/1.00  fof(f55,plain,(
% 3.66/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.66/1.00    inference(cnf_transformation,[],[f37])).
% 3.66/1.00  
% 3.66/1.00  fof(f101,plain,(
% 3.66/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 3.66/1.00    inference(definition_unfolding,[],[f55,f59])).
% 3.66/1.00  
% 3.66/1.00  fof(f105,plain,(
% 3.66/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 3.66/1.00    inference(equality_resolution,[],[f101])).
% 3.66/1.00  
% 3.66/1.00  fof(f95,plain,(
% 3.66/1.00    m1_subset_1(sK9,u1_struct_0(sK5))),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f7,axiom,(
% 3.66/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f20,plain,(
% 3.66/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f7])).
% 3.66/1.00  
% 3.66/1.00  fof(f21,plain,(
% 3.66/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.66/1.00    inference(flattening,[],[f20])).
% 3.66/1.00  
% 3.66/1.00  fof(f69,plain,(
% 3.66/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f21])).
% 3.66/1.00  
% 3.66/1.00  fof(f83,plain,(
% 3.66/1.00    ~v2_struct_0(sK5)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f84,plain,(
% 3.66/1.00    v2_pre_topc(sK5)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f85,plain,(
% 3.66/1.00    l1_pre_topc(sK5)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f87,plain,(
% 3.66/1.00    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f12,axiom,(
% 3.66/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f30,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f12])).
% 3.66/1.00  
% 3.66/1.00  fof(f31,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/1.00    inference(flattening,[],[f30])).
% 3.66/1.00  
% 3.66/1.00  fof(f76,plain,(
% 3.66/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f31])).
% 3.66/1.00  
% 3.66/1.00  fof(f109,plain,(
% 3.66/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/1.00    inference(equality_resolution,[],[f76])).
% 3.66/1.00  
% 3.66/1.00  fof(f97,plain,(
% 3.66/1.00    ~r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f77,plain,(
% 3.66/1.00    ~v2_struct_0(sK3)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f78,plain,(
% 3.66/1.00    v2_pre_topc(sK3)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f79,plain,(
% 3.66/1.00    l1_pre_topc(sK3)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f89,plain,(
% 3.66/1.00    v1_funct_1(sK7)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f90,plain,(
% 3.66/1.00    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f91,plain,(
% 3.66/1.00    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f11,axiom,(
% 3.66/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 3.66/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.00  
% 3.66/1.00  fof(f28,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/1.00    inference(ennf_transformation,[],[f11])).
% 3.66/1.00  
% 3.66/1.00  fof(f29,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/1.00    inference(flattening,[],[f28])).
% 3.66/1.00  
% 3.66/1.00  fof(f43,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/1.00    inference(nnf_transformation,[],[f29])).
% 3.66/1.00  
% 3.66/1.00  fof(f44,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/1.00    inference(rectify,[],[f43])).
% 3.66/1.00  
% 3.66/1.00  fof(f45,plain,(
% 3.66/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.66/1.00    introduced(choice_axiom,[])).
% 3.66/1.00  
% 3.66/1.00  fof(f46,plain,(
% 3.66/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 3.66/1.00  
% 3.66/1.00  fof(f73,plain,(
% 3.66/1.00    ( ! [X4,X2,X0,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~v5_pre_topc(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/1.00    inference(cnf_transformation,[],[f46])).
% 3.66/1.00  
% 3.66/1.00  fof(f93,plain,(
% 3.66/1.00    v5_pre_topc(sK6,sK5,sK4)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  fof(f94,plain,(
% 3.66/1.00    r1_tmap_1(sK4,sK3,sK7,sK8)),
% 3.66/1.00    inference(cnf_transformation,[],[f54])).
% 3.66/1.00  
% 3.66/1.00  cnf(c_26,negated_conjecture,
% 3.66/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 3.66/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1949,plain,
% 3.66/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_14,plain,
% 3.66/1.00      ( ~ m1_subset_1(X0,X1)
% 3.66/1.00      | v1_xboole_0(X1)
% 3.66/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.66/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1957,plain,
% 3.66/1.00      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 3.66/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.66/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_3510,plain,
% 3.66/1.00      ( k6_domain_1(u1_struct_0(sK4),sK8) = k2_tarski(sK8,sK8)
% 3.66/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1949,c_1957]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_16,plain,
% 3.66/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.66/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 3.66/1.00      | v2_struct_0(X1)
% 3.66/1.00      | ~ v2_pre_topc(X1)
% 3.66/1.00      | ~ l1_pre_topc(X1) ),
% 3.66/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1955,plain,
% 3.66/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.66/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0)) = iProver_top
% 3.66/1.00      | v2_struct_0(X1) = iProver_top
% 3.66/1.00      | v2_pre_topc(X1) != iProver_top
% 3.66/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_15,plain,
% 3.66/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.66/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.66/1.00      | v2_struct_0(X1)
% 3.66/1.00      | ~ v2_pre_topc(X1)
% 3.66/1.00      | ~ l1_pre_topc(X1) ),
% 3.66/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1956,plain,
% 3.66/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.66/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.66/1.00      | v2_struct_0(X1) = iProver_top
% 3.66/1.00      | v2_pre_topc(X1) != iProver_top
% 3.66/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_4,plain,
% 3.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.66/1.00      | ~ r2_hidden(X2,X0)
% 3.66/1.00      | ~ v1_xboole_0(X1) ),
% 3.66/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1967,plain,
% 3.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.66/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.66/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_5698,plain,
% 3.66/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.66/1.00      | r2_hidden(X2,k1_connsp_2(X1,X0)) != iProver_top
% 3.66/1.00      | v2_struct_0(X1) = iProver_top
% 3.66/1.00      | v2_pre_topc(X1) != iProver_top
% 3.66/1.00      | l1_pre_topc(X1) != iProver_top
% 3.66/1.00      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1956,c_1967]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_7221,plain,
% 3.66/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.66/1.00      | v2_struct_0(X1) = iProver_top
% 3.66/1.00      | v2_pre_topc(X1) != iProver_top
% 3.66/1.00      | l1_pre_topc(X1) != iProver_top
% 3.66/1.00      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1955,c_5698]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_7421,plain,
% 3.66/1.00      ( v2_struct_0(sK4) = iProver_top
% 3.66/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.66/1.00      | l1_pre_topc(sK4) != iProver_top
% 3.66/1.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1949,c_7221]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_38,negated_conjecture,
% 3.66/1.00      ( ~ v2_struct_0(sK4) ),
% 3.66/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_45,plain,
% 3.66/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_37,negated_conjecture,
% 3.66/1.00      ( v2_pre_topc(sK4) ),
% 3.66/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_46,plain,
% 3.66/1.00      ( v2_pre_topc(sK4) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_36,negated_conjecture,
% 3.66/1.00      ( l1_pre_topc(sK4) ),
% 3.66/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_47,plain,
% 3.66/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_8572,plain,
% 3.66/1.00      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.66/1.00      inference(global_propositional_subsumption,
% 3.66/1.00                [status(thm)],
% 3.66/1.00                [c_7421,c_45,c_46,c_47]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_8577,plain,
% 3.66/1.00      ( k6_domain_1(u1_struct_0(sK4),sK8) = k2_tarski(sK8,sK8) ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_3510,c_8572]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_30,negated_conjecture,
% 3.66/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
% 3.66/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1945,plain,
% 3.66/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_12,plain,
% 3.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.66/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1959,plain,
% 3.66/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.66/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_4101,plain,
% 3.66/1.00      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k10_relat_1(sK6,X0) ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1945,c_1959]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_22,negated_conjecture,
% 3.66/1.00      ( r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) ),
% 3.66/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1952,plain,
% 3.66/1.00      ( r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_4888,plain,
% 3.66/1.00      ( r2_hidden(sK9,k10_relat_1(sK6,k6_domain_1(u1_struct_0(sK4),sK8))) = iProver_top ),
% 3.66/1.00      inference(demodulation,[status(thm)],[c_4101,c_1952]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_9,plain,
% 3.66/1.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.66/1.00      | r2_hidden(k1_funct_1(X1,X0),X2)
% 3.66/1.00      | ~ v1_relat_1(X1)
% 3.66/1.00      | ~ v1_funct_1(X1) ),
% 3.66/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1962,plain,
% 3.66/1.00      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.66/1.00      | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
% 3.66/1.00      | v1_relat_1(X1) != iProver_top
% 3.66/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_5644,plain,
% 3.66/1.00      ( r2_hidden(k1_funct_1(sK6,sK9),k6_domain_1(u1_struct_0(sK4),sK8)) = iProver_top
% 3.66/1.00      | v1_relat_1(sK6) != iProver_top
% 3.66/1.00      | v1_funct_1(sK6) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_4888,c_1962]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_32,negated_conjecture,
% 3.66/1.00      ( v1_funct_1(sK6) ),
% 3.66/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_51,plain,
% 3.66/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_53,plain,
% 3.66/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_11,plain,
% 3.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.00      | v1_relat_1(X0) ),
% 3.66/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_2336,plain,
% 3.66/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.66/1.00      | v1_relat_1(sK6) ),
% 3.66/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_2337,plain,
% 3.66/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
% 3.66/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2336]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_6546,plain,
% 3.66/1.00      ( r2_hidden(k1_funct_1(sK6,sK9),k6_domain_1(u1_struct_0(sK4),sK8)) = iProver_top ),
% 3.66/1.00      inference(global_propositional_subsumption,
% 3.66/1.00                [status(thm)],
% 3.66/1.00                [c_5644,c_51,c_53,c_2337]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_8987,plain,
% 3.66/1.00      ( r2_hidden(k1_funct_1(sK6,sK9),k2_tarski(sK8,sK8)) = iProver_top ),
% 3.66/1.00      inference(demodulation,[status(thm)],[c_8577,c_6546]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_3,plain,
% 3.66/1.00      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 3.66/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1968,plain,
% 3.66/1.00      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_10546,plain,
% 3.66/1.00      ( k1_funct_1(sK6,sK9) = sK8 ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_8987,c_1968]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_23,negated_conjecture,
% 3.66/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
% 3.66/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1951,plain,
% 3.66/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_13,plain,
% 3.66/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/1.00      | ~ m1_subset_1(X3,X1)
% 3.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.00      | ~ v1_funct_1(X0)
% 3.66/1.00      | v1_xboole_0(X1)
% 3.66/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.66/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1958,plain,
% 3.66/1.00      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 3.66/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.66/1.00      | m1_subset_1(X3,X0) != iProver_top
% 3.66/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.66/1.00      | v1_funct_1(X2) != iProver_top
% 3.66/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_7449,plain,
% 3.66/1.00      ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k1_funct_1(sK6,X0)
% 3.66/1.00      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.66/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.66/1.00      | v1_funct_1(sK6) != iProver_top
% 3.66/1.00      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1945,c_1958]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_35,negated_conjecture,
% 3.66/1.00      ( ~ v2_struct_0(sK5) ),
% 3.66/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_48,plain,
% 3.66/1.00      ( v2_struct_0(sK5) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_34,negated_conjecture,
% 3.66/1.00      ( v2_pre_topc(sK5) ),
% 3.66/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_49,plain,
% 3.66/1.00      ( v2_pre_topc(sK5) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_33,negated_conjecture,
% 3.66/1.00      ( l1_pre_topc(sK5) ),
% 3.66/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_50,plain,
% 3.66/1.00      ( l1_pre_topc(sK5) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_31,negated_conjecture,
% 3.66/1.00      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
% 3.66/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_52,plain,
% 3.66/1.00      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_7420,plain,
% 3.66/1.00      ( v2_struct_0(sK5) = iProver_top
% 3.66/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.66/1.00      | l1_pre_topc(sK5) != iProver_top
% 3.66/1.00      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1951,c_7221]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_8897,plain,
% 3.66/1.00      ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k1_funct_1(sK6,X0)
% 3.66/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.66/1.00      inference(global_propositional_subsumption,
% 3.66/1.00                [status(thm)],
% 3.66/1.00                [c_7449,c_48,c_49,c_50,c_51,c_52,c_7420]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_8905,plain,
% 3.66/1.00      ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9) = k1_funct_1(sK6,sK9) ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1951,c_8897]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_20,plain,
% 3.66/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.66/1.00      | ~ r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 3.66/1.00      | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3)
% 3.66/1.00      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 3.66/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.66/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.66/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.66/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.66/1.00      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1))
% 3.66/1.00      | v2_struct_0(X4)
% 3.66/1.00      | v2_struct_0(X0)
% 3.66/1.00      | v2_struct_0(X1)
% 3.66/1.00      | ~ v2_pre_topc(X4)
% 3.66/1.00      | ~ v2_pre_topc(X0)
% 3.66/1.00      | ~ v2_pre_topc(X1)
% 3.66/1.00      | ~ l1_pre_topc(X4)
% 3.66/1.00      | ~ l1_pre_topc(X0)
% 3.66/1.00      | ~ l1_pre_topc(X1)
% 3.66/1.00      | ~ v1_funct_1(X2)
% 3.66/1.00      | ~ v1_funct_1(X5) ),
% 3.66/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1954,plain,
% 3.66/1.00      ( r1_tmap_1(X0,X1,X2,X3) != iProver_top
% 3.66/1.00      | r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != iProver_top
% 3.66/1.00      | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3) = iProver_top
% 3.66/1.00      | v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)) != iProver_top
% 3.66/1.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.66/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.66/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) != iProver_top
% 3.66/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.66/1.00      | m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1)) != iProver_top
% 3.66/1.00      | v2_struct_0(X4) = iProver_top
% 3.66/1.00      | v2_struct_0(X0) = iProver_top
% 3.66/1.00      | v2_struct_0(X1) = iProver_top
% 3.66/1.00      | v2_pre_topc(X4) != iProver_top
% 3.66/1.00      | v2_pre_topc(X0) != iProver_top
% 3.66/1.00      | v2_pre_topc(X1) != iProver_top
% 3.66/1.00      | l1_pre_topc(X4) != iProver_top
% 3.66/1.00      | l1_pre_topc(X0) != iProver_top
% 3.66/1.00      | l1_pre_topc(X1) != iProver_top
% 3.66/1.00      | v1_funct_1(X2) != iProver_top
% 3.66/1.00      | v1_funct_1(X5) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_21,negated_conjecture,
% 3.66/1.00      ( ~ r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) ),
% 3.66/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_1953,plain,
% 3.66/1.00      ( r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_5636,plain,
% 3.66/1.00      ( r1_tmap_1(sK4,sK3,sK7,k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9)) != iProver_top
% 3.66/1.00      | r1_tmap_1(sK5,sK4,sK6,sK9) != iProver_top
% 3.66/1.00      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.66/1.00      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.66/1.00      | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9),u1_struct_0(sK4)) != iProver_top
% 3.66/1.00      | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
% 3.66/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.66/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
% 3.66/1.00      | v2_struct_0(sK4) = iProver_top
% 3.66/1.00      | v2_struct_0(sK3) = iProver_top
% 3.66/1.00      | v2_struct_0(sK5) = iProver_top
% 3.66/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.66/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.66/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.66/1.00      | l1_pre_topc(sK4) != iProver_top
% 3.66/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.66/1.00      | l1_pre_topc(sK5) != iProver_top
% 3.66/1.00      | v1_funct_1(sK7) != iProver_top
% 3.66/1.00      | v1_funct_1(sK6) != iProver_top ),
% 3.66/1.00      inference(superposition,[status(thm)],[c_1954,c_1953]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_41,negated_conjecture,
% 3.66/1.00      ( ~ v2_struct_0(sK3) ),
% 3.66/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_42,plain,
% 3.66/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_40,negated_conjecture,
% 3.66/1.00      ( v2_pre_topc(sK3) ),
% 3.66/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_43,plain,
% 3.66/1.00      ( v2_pre_topc(sK3) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_39,negated_conjecture,
% 3.66/1.00      ( l1_pre_topc(sK3) ),
% 3.66/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_44,plain,
% 3.66/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_29,negated_conjecture,
% 3.66/1.00      ( v1_funct_1(sK7) ),
% 3.66/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_54,plain,
% 3.66/1.00      ( v1_funct_1(sK7) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_28,negated_conjecture,
% 3.66/1.00      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 3.66/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_55,plain,
% 3.66/1.00      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_27,negated_conjecture,
% 3.66/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.66/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_56,plain,
% 3.66/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_60,plain,
% 3.66/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_19,plain,
% 3.66/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.66/1.00      | ~ v5_pre_topc(X2,X0,X1)
% 3.66/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.66/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.66/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.66/1.00      | v2_struct_0(X1)
% 3.66/1.00      | v2_struct_0(X0)
% 3.66/1.00      | ~ v2_pre_topc(X1)
% 3.66/1.00      | ~ v2_pre_topc(X0)
% 3.66/1.00      | ~ l1_pre_topc(X1)
% 3.66/1.00      | ~ l1_pre_topc(X0)
% 3.66/1.00      | ~ v1_funct_1(X2) ),
% 3.66/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_25,negated_conjecture,
% 3.66/1.00      ( v5_pre_topc(sK6,sK5,sK4) ),
% 3.66/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_729,plain,
% 3.66/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.66/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.66/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.66/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.66/1.00      | v2_struct_0(X0)
% 3.66/1.00      | v2_struct_0(X1)
% 3.66/1.00      | ~ v2_pre_topc(X0)
% 3.66/1.00      | ~ v2_pre_topc(X1)
% 3.66/1.00      | ~ l1_pre_topc(X0)
% 3.66/1.00      | ~ l1_pre_topc(X1)
% 3.66/1.00      | ~ v1_funct_1(X2)
% 3.66/1.00      | sK6 != X2
% 3.66/1.00      | sK4 != X1
% 3.66/1.00      | sK5 != X0 ),
% 3.66/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_730,plain,
% 3.66/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0)
% 3.66/1.00      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
% 3.66/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.66/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.66/1.00      | v2_struct_0(sK4)
% 3.66/1.00      | v2_struct_0(sK5)
% 3.66/1.00      | ~ v2_pre_topc(sK4)
% 3.66/1.00      | ~ v2_pre_topc(sK5)
% 3.66/1.00      | ~ l1_pre_topc(sK4)
% 3.66/1.00      | ~ l1_pre_topc(sK5)
% 3.66/1.00      | ~ v1_funct_1(sK6) ),
% 3.66/1.00      inference(unflattening,[status(thm)],[c_729]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_734,plain,
% 3.66/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0) | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.66/1.00      inference(global_propositional_subsumption,
% 3.66/1.00                [status(thm)],
% 3.66/1.00                [c_730,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31,c_30]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_2330,plain,
% 3.66/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9)
% 3.66/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK5)) ),
% 3.66/1.00      inference(instantiation,[status(thm)],[c_734]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_2331,plain,
% 3.66/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9) = iProver_top
% 3.66/1.00      | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_2330]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_6282,plain,
% 3.66/1.00      ( r1_tmap_1(sK4,sK3,sK7,k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9)) != iProver_top
% 3.66/1.00      | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9),u1_struct_0(sK4)) != iProver_top ),
% 3.66/1.00      inference(global_propositional_subsumption,
% 3.66/1.00                [status(thm)],
% 3.66/1.00                [c_5636,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,
% 3.66/1.00                 c_51,c_52,c_53,c_54,c_55,c_56,c_60,c_2331]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_8909,plain,
% 3.66/1.00      ( r1_tmap_1(sK4,sK3,sK7,k1_funct_1(sK6,sK9)) != iProver_top
% 3.66/1.00      | m1_subset_1(k1_funct_1(sK6,sK9),u1_struct_0(sK4)) != iProver_top ),
% 3.66/1.00      inference(demodulation,[status(thm)],[c_8905,c_6282]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_10755,plain,
% 3.66/1.00      ( r1_tmap_1(sK4,sK3,sK7,sK8) != iProver_top
% 3.66/1.00      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
% 3.66/1.00      inference(demodulation,[status(thm)],[c_10546,c_8909]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_24,negated_conjecture,
% 3.66/1.00      ( r1_tmap_1(sK4,sK3,sK7,sK8) ),
% 3.66/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_59,plain,
% 3.66/1.00      ( r1_tmap_1(sK4,sK3,sK7,sK8) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(c_57,plain,
% 3.66/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.66/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.66/1.00  
% 3.66/1.00  cnf(contradiction,plain,
% 3.66/1.00      ( $false ),
% 3.66/1.00      inference(minisat,[status(thm)],[c_10755,c_59,c_57]) ).
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/1.00  
% 3.66/1.00  ------                               Statistics
% 3.66/1.00  
% 3.66/1.00  ------ General
% 3.66/1.00  
% 3.66/1.00  abstr_ref_over_cycles:                  0
% 3.66/1.00  abstr_ref_under_cycles:                 0
% 3.66/1.00  gc_basic_clause_elim:                   0
% 3.66/1.00  forced_gc_time:                         0
% 3.66/1.00  parsing_time:                           0.012
% 3.66/1.00  unif_index_cands_time:                  0.
% 3.66/1.00  unif_index_add_time:                    0.
% 3.66/1.00  orderings_time:                         0.
% 3.66/1.00  out_proof_time:                         0.013
% 3.66/1.00  total_time:                             0.366
% 3.66/1.00  num_of_symbols:                         64
% 3.66/1.00  num_of_terms:                           12283
% 3.66/1.00  
% 3.66/1.00  ------ Preprocessing
% 3.66/1.00  
% 3.66/1.00  num_of_splits:                          0
% 3.66/1.00  num_of_split_atoms:                     0
% 3.66/1.00  num_of_reused_defs:                     0
% 3.66/1.00  num_eq_ax_congr_red:                    60
% 3.66/1.00  num_of_sem_filtered_clauses:            1
% 3.66/1.00  num_of_subtypes:                        0
% 3.66/1.00  monotx_restored_types:                  0
% 3.66/1.00  sat_num_of_epr_types:                   0
% 3.66/1.00  sat_num_of_non_cyclic_types:            0
% 3.66/1.00  sat_guarded_non_collapsed_types:        0
% 3.66/1.00  num_pure_diseq_elim:                    0
% 3.66/1.00  simp_replaced_by:                       0
% 3.66/1.00  res_preprocessed:                       202
% 3.66/1.00  prep_upred:                             0
% 3.66/1.00  prep_unflattend:                        12
% 3.66/1.00  smt_new_axioms:                         0
% 3.66/1.00  pred_elim_cands:                        10
% 3.66/1.00  pred_elim:                              1
% 3.66/1.00  pred_elim_cl:                           1
% 3.66/1.00  pred_elim_cycles:                       6
% 3.66/1.00  merged_defs:                            0
% 3.66/1.00  merged_defs_ncl:                        0
% 3.66/1.00  bin_hyper_res:                          0
% 3.66/1.00  prep_cycles:                            4
% 3.66/1.00  pred_elim_time:                         0.011
% 3.66/1.00  splitting_time:                         0.
% 3.66/1.00  sem_filter_time:                        0.
% 3.66/1.00  monotx_time:                            0.002
% 3.66/1.00  subtype_inf_time:                       0.
% 3.66/1.00  
% 3.66/1.00  ------ Problem properties
% 3.66/1.00  
% 3.66/1.00  clauses:                                41
% 3.66/1.00  conjectures:                            20
% 3.66/1.00  epr:                                    12
% 3.66/1.00  horn:                                   31
% 3.66/1.00  ground:                                 20
% 3.66/1.00  unary:                                  21
% 3.66/1.00  binary:                                 4
% 3.66/1.00  lits:                                   130
% 3.66/1.00  lits_eq:                                11
% 3.66/1.00  fd_pure:                                0
% 3.66/1.00  fd_pseudo:                              0
% 3.66/1.00  fd_cond:                                0
% 3.66/1.00  fd_pseudo_cond:                         5
% 3.66/1.00  ac_symbols:                             0
% 3.66/1.00  
% 3.66/1.00  ------ Propositional Solver
% 3.66/1.00  
% 3.66/1.00  prop_solver_calls:                      27
% 3.66/1.00  prop_fast_solver_calls:                 1727
% 3.66/1.00  smt_solver_calls:                       0
% 3.66/1.00  smt_fast_solver_calls:                  0
% 3.66/1.00  prop_num_of_clauses:                    4181
% 3.66/1.00  prop_preprocess_simplified:             12218
% 3.66/1.00  prop_fo_subsumed:                       59
% 3.66/1.00  prop_solver_time:                       0.
% 3.66/1.00  smt_solver_time:                        0.
% 3.66/1.00  smt_fast_solver_time:                   0.
% 3.66/1.00  prop_fast_solver_time:                  0.
% 3.66/1.00  prop_unsat_core_time:                   0.
% 3.66/1.00  
% 3.66/1.00  ------ QBF
% 3.66/1.00  
% 3.66/1.00  qbf_q_res:                              0
% 3.66/1.00  qbf_num_tautologies:                    0
% 3.66/1.00  qbf_prep_cycles:                        0
% 3.66/1.00  
% 3.66/1.00  ------ BMC1
% 3.66/1.00  
% 3.66/1.00  bmc1_current_bound:                     -1
% 3.66/1.00  bmc1_last_solved_bound:                 -1
% 3.66/1.00  bmc1_unsat_core_size:                   -1
% 3.66/1.00  bmc1_unsat_core_parents_size:           -1
% 3.66/1.00  bmc1_merge_next_fun:                    0
% 3.66/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.66/1.00  
% 3.66/1.00  ------ Instantiation
% 3.66/1.00  
% 3.66/1.00  inst_num_of_clauses:                    1142
% 3.66/1.00  inst_num_in_passive:                    670
% 3.66/1.00  inst_num_in_active:                     400
% 3.66/1.00  inst_num_in_unprocessed:                72
% 3.66/1.00  inst_num_of_loops:                      440
% 3.66/1.00  inst_num_of_learning_restarts:          0
% 3.66/1.00  inst_num_moves_active_passive:          39
% 3.66/1.00  inst_lit_activity:                      0
% 3.66/1.00  inst_lit_activity_moves:                0
% 3.66/1.00  inst_num_tautologies:                   0
% 3.66/1.00  inst_num_prop_implied:                  0
% 3.66/1.00  inst_num_existing_simplified:           0
% 3.66/1.00  inst_num_eq_res_simplified:             0
% 3.66/1.00  inst_num_child_elim:                    0
% 3.66/1.00  inst_num_of_dismatching_blockings:      199
% 3.66/1.00  inst_num_of_non_proper_insts:           642
% 3.66/1.00  inst_num_of_duplicates:                 0
% 3.66/1.00  inst_inst_num_from_inst_to_res:         0
% 3.66/1.00  inst_dismatching_checking_time:         0.
% 3.66/1.00  
% 3.66/1.00  ------ Resolution
% 3.66/1.00  
% 3.66/1.00  res_num_of_clauses:                     0
% 3.66/1.00  res_num_in_passive:                     0
% 3.66/1.00  res_num_in_active:                      0
% 3.66/1.00  res_num_of_loops:                       206
% 3.66/1.00  res_forward_subset_subsumed:            62
% 3.66/1.00  res_backward_subset_subsumed:           0
% 3.66/1.00  res_forward_subsumed:                   0
% 3.66/1.00  res_backward_subsumed:                  0
% 3.66/1.00  res_forward_subsumption_resolution:     0
% 3.66/1.00  res_backward_subsumption_resolution:    0
% 3.66/1.00  res_clause_to_clause_subsumption:       639
% 3.66/1.00  res_orphan_elimination:                 0
% 3.66/1.00  res_tautology_del:                      22
% 3.66/1.00  res_num_eq_res_simplified:              0
% 3.66/1.00  res_num_sel_changes:                    0
% 3.66/1.00  res_moves_from_active_to_pass:          0
% 3.66/1.00  
% 3.66/1.00  ------ Superposition
% 3.66/1.00  
% 3.66/1.00  sup_time_total:                         0.
% 3.66/1.00  sup_time_generating:                    0.
% 3.66/1.00  sup_time_sim_full:                      0.
% 3.66/1.00  sup_time_sim_immed:                     0.
% 3.66/1.00  
% 3.66/1.00  sup_num_of_clauses:                     135
% 3.66/1.00  sup_num_in_active:                      71
% 3.66/1.00  sup_num_in_passive:                     64
% 3.66/1.00  sup_num_of_loops:                       86
% 3.66/1.00  sup_fw_superposition:                   77
% 3.66/1.00  sup_bw_superposition:                   70
% 3.66/1.00  sup_immediate_simplified:               22
% 3.66/1.00  sup_given_eliminated:                   2
% 3.66/1.00  comparisons_done:                       0
% 3.66/1.00  comparisons_avoided:                    7
% 3.66/1.00  
% 3.66/1.00  ------ Simplifications
% 3.66/1.00  
% 3.66/1.00  
% 3.66/1.00  sim_fw_subset_subsumed:                 9
% 3.66/1.00  sim_bw_subset_subsumed:                 3
% 3.66/1.00  sim_fw_subsumed:                        13
% 3.66/1.00  sim_bw_subsumed:                        1
% 3.66/1.00  sim_fw_subsumption_res:                 1
% 3.66/1.00  sim_bw_subsumption_res:                 0
% 3.66/1.00  sim_tautology_del:                      5
% 3.66/1.00  sim_eq_tautology_del:                   1
% 3.66/1.00  sim_eq_res_simp:                        1
% 3.66/1.00  sim_fw_demodulated:                     0
% 3.66/1.00  sim_bw_demodulated:                     12
% 3.66/1.00  sim_light_normalised:                   0
% 3.66/1.00  sim_joinable_taut:                      0
% 3.66/1.00  sim_joinable_simp:                      0
% 3.66/1.00  sim_ac_normalised:                      0
% 3.66/1.00  sim_smt_subsumption:                    0
% 3.66/1.00  
%------------------------------------------------------------------------------
