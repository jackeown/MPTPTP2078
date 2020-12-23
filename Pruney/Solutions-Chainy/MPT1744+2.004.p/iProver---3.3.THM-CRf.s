%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:17 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 852 expanded)
%              Number of clauses        :  110 ( 156 expanded)
%              Number of leaves         :   24 ( 399 expanded)
%              Depth                    :   16
%              Number of atoms          : 1077 (13827 expanded)
%              Number of equality atoms :  233 ( 249 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   42 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
          & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),sK9)
        & r2_hidden(sK9,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
        & m1_subset_1(sK9,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f34,f54,f53,f52,f51,f50,f49,f48])).

fof(f94,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f72,f60])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f88,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f107,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f103])).

fof(f97,plain,(
    m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f111,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f99,plain,(
    ~ r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f55])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    v5_pre_topc(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    r1_tmap_1(sK4,sK3,sK7,sK8) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1705,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1713,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3520,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK8) = k2_tarski(sK8,sK8)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1713])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1711,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,k1_connsp_2(X1,X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1712,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1724,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5201,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X2,k1_connsp_2(X1,X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1712,c_1724])).

cnf(c_6560,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_5201])).

cnf(c_9017,plain,
    ( v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_6560])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_47,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_48,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_58,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2151,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2152,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2151])).

cnf(c_2157,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK4))
    | r2_hidden(sK8,k1_connsp_2(sK4,sK8))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2158,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK8,k1_connsp_2(sK4,sK8)) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2157])).

cnf(c_2323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3982,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,k1_connsp_2(sK4,sK8))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2323])).

cnf(c_5192,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK8,k1_connsp_2(sK4,sK8))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3982])).

cnf(c_5193,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK8,k1_connsp_2(sK4,sK8)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5192])).

cnf(c_9168,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9017,c_46,c_47,c_48,c_58,c_2152,c_2158,c_5193])).

cnf(c_9173,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK8) = k2_tarski(sK8,sK8) ),
    inference(superposition,[status(thm)],[c_3520,c_9168])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1701,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1715,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3100,plain,
    ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k10_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1701,c_1715])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1708,plain,
    ( r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3217,plain,
    ( r2_hidden(sK9,k10_relat_1(sK6,k6_domain_1(u1_struct_0(sK4),sK8))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3100,c_1708])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1717,plain,
    ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5162,plain,
    ( r2_hidden(k1_funct_1(sK6,sK9),k6_domain_1(u1_struct_0(sK4),sK8)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3217,c_1717])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_52,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1723,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3018,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_1723])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3032,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3033,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3032])).

cnf(c_5525,plain,
    ( r2_hidden(k1_funct_1(sK6,sK9),k6_domain_1(u1_struct_0(sK4),sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5162,c_52,c_3018,c_3033])).

cnf(c_9424,plain,
    ( r2_hidden(k1_funct_1(sK6,sK9),k2_tarski(sK8,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9173,c_5525])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1725,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9594,plain,
    ( k1_funct_1(sK6,sK9) = sK8 ),
    inference(superposition,[status(thm)],[c_9424,c_1725])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1707,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1714,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6592,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k1_funct_1(sK6,X0)
    | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_1714])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_49,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_50,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_51,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_53,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_61,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2148,plain,
    ( m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2149,plain,
    ( m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2148])).

cnf(c_2154,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | r2_hidden(sK9,k1_connsp_2(sK5,sK9))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2155,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK9,k1_connsp_2(sK5,sK9)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2154])).

cnf(c_2318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3953,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,k1_connsp_2(sK5,sK9))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2318])).

cnf(c_5189,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK9,k1_connsp_2(sK5,sK9))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3953])).

cnf(c_5190,plain,
    ( m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK9,k1_connsp_2(sK5,sK9)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5189])).

cnf(c_7674,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k1_funct_1(sK6,X0)
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6592,c_49,c_50,c_51,c_52,c_53,c_61,c_2149,c_2155,c_5190])).

cnf(c_7682,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9) = k1_funct_1(sK6,sK9) ),
    inference(superposition,[status(thm)],[c_1707,c_7674])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f111])).

cnf(c_1710,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1709,plain,
    ( r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4856,plain,
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
    inference(superposition,[status(thm)],[c_1710,c_1709])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_44,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_54,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_55,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_56,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_57,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( v5_pre_topc(sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_589,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_590,plain,
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
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_594,plain,
    ( r1_tmap_1(sK5,sK4,sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_590,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31])).

cnf(c_2094,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_2095,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_5250,plain,
    ( r1_tmap_1(sK4,sK3,sK7,k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9)) != iProver_top
    | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9),u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4856,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_61,c_2095])).

cnf(c_7686,plain,
    ( r1_tmap_1(sK4,sK3,sK7,k1_funct_1(sK6,sK9)) != iProver_top
    | m1_subset_1(k1_funct_1(sK6,sK9),u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7682,c_5250])).

cnf(c_9761,plain,
    ( r1_tmap_1(sK4,sK3,sK7,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9594,c_7686])).

cnf(c_25,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,sK7,sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_60,plain,
    ( r1_tmap_1(sK4,sK3,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9761,c_60,c_58])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:07:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.59/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/1.00  
% 3.59/1.00  ------  iProver source info
% 3.59/1.00  
% 3.59/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.59/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/1.00  git: non_committed_changes: false
% 3.59/1.00  git: last_make_outside_of_git: false
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     num_symb
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       true
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  ------ Parsing...
% 3.59/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/1.00  ------ Proving...
% 3.59/1.00  ------ Problem Properties 
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  clauses                                 42
% 3.59/1.00  conjectures                             20
% 3.59/1.00  EPR                                     12
% 3.59/1.00  Horn                                    32
% 3.59/1.00  unary                                   22
% 3.59/1.00  binary                                  3
% 3.59/1.00  lits                                    132
% 3.59/1.00  lits eq                                 11
% 3.59/1.00  fd_pure                                 0
% 3.59/1.00  fd_pseudo                               0
% 3.59/1.00  fd_cond                                 0
% 3.59/1.00  fd_pseudo_cond                          5
% 3.59/1.00  AC symbols                              0
% 3.59/1.00  
% 3.59/1.00  ------ Schedule dynamic 5 is on 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ 
% 3.59/1.00  Current options:
% 3.59/1.00  ------ 
% 3.59/1.00  
% 3.59/1.00  ------ Input Options
% 3.59/1.00  
% 3.59/1.00  --out_options                           all
% 3.59/1.00  --tptp_safe_out                         true
% 3.59/1.00  --problem_path                          ""
% 3.59/1.00  --include_path                          ""
% 3.59/1.00  --clausifier                            res/vclausify_rel
% 3.59/1.00  --clausifier_options                    --mode clausify
% 3.59/1.00  --stdin                                 false
% 3.59/1.00  --stats_out                             all
% 3.59/1.00  
% 3.59/1.00  ------ General Options
% 3.59/1.00  
% 3.59/1.00  --fof                                   false
% 3.59/1.00  --time_out_real                         305.
% 3.59/1.00  --time_out_virtual                      -1.
% 3.59/1.00  --symbol_type_check                     false
% 3.59/1.00  --clausify_out                          false
% 3.59/1.00  --sig_cnt_out                           false
% 3.59/1.00  --trig_cnt_out                          false
% 3.59/1.00  --trig_cnt_out_tolerance                1.
% 3.59/1.00  --trig_cnt_out_sk_spl                   false
% 3.59/1.00  --abstr_cl_out                          false
% 3.59/1.00  
% 3.59/1.00  ------ Global Options
% 3.59/1.00  
% 3.59/1.00  --schedule                              default
% 3.59/1.00  --add_important_lit                     false
% 3.59/1.00  --prop_solver_per_cl                    1000
% 3.59/1.00  --min_unsat_core                        false
% 3.59/1.00  --soft_assumptions                      false
% 3.59/1.00  --soft_lemma_size                       3
% 3.59/1.00  --prop_impl_unit_size                   0
% 3.59/1.00  --prop_impl_unit                        []
% 3.59/1.00  --share_sel_clauses                     true
% 3.59/1.00  --reset_solvers                         false
% 3.59/1.00  --bc_imp_inh                            [conj_cone]
% 3.59/1.00  --conj_cone_tolerance                   3.
% 3.59/1.00  --extra_neg_conj                        none
% 3.59/1.00  --large_theory_mode                     true
% 3.59/1.00  --prolific_symb_bound                   200
% 3.59/1.00  --lt_threshold                          2000
% 3.59/1.00  --clause_weak_htbl                      true
% 3.59/1.00  --gc_record_bc_elim                     false
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing Options
% 3.59/1.00  
% 3.59/1.00  --preprocessing_flag                    true
% 3.59/1.00  --time_out_prep_mult                    0.1
% 3.59/1.00  --splitting_mode                        input
% 3.59/1.00  --splitting_grd                         true
% 3.59/1.00  --splitting_cvd                         false
% 3.59/1.00  --splitting_cvd_svl                     false
% 3.59/1.00  --splitting_nvd                         32
% 3.59/1.00  --sub_typing                            true
% 3.59/1.00  --prep_gs_sim                           true
% 3.59/1.00  --prep_unflatten                        true
% 3.59/1.00  --prep_res_sim                          true
% 3.59/1.00  --prep_upred                            true
% 3.59/1.00  --prep_sem_filter                       exhaustive
% 3.59/1.00  --prep_sem_filter_out                   false
% 3.59/1.00  --pred_elim                             true
% 3.59/1.00  --res_sim_input                         true
% 3.59/1.00  --eq_ax_congr_red                       true
% 3.59/1.00  --pure_diseq_elim                       true
% 3.59/1.00  --brand_transform                       false
% 3.59/1.00  --non_eq_to_eq                          false
% 3.59/1.00  --prep_def_merge                        true
% 3.59/1.00  --prep_def_merge_prop_impl              false
% 3.59/1.00  --prep_def_merge_mbd                    true
% 3.59/1.00  --prep_def_merge_tr_red                 false
% 3.59/1.00  --prep_def_merge_tr_cl                  false
% 3.59/1.00  --smt_preprocessing                     true
% 3.59/1.00  --smt_ac_axioms                         fast
% 3.59/1.00  --preprocessed_out                      false
% 3.59/1.00  --preprocessed_stats                    false
% 3.59/1.00  
% 3.59/1.00  ------ Abstraction refinement Options
% 3.59/1.00  
% 3.59/1.00  --abstr_ref                             []
% 3.59/1.00  --abstr_ref_prep                        false
% 3.59/1.00  --abstr_ref_until_sat                   false
% 3.59/1.00  --abstr_ref_sig_restrict                funpre
% 3.59/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.00  --abstr_ref_under                       []
% 3.59/1.00  
% 3.59/1.00  ------ SAT Options
% 3.59/1.00  
% 3.59/1.00  --sat_mode                              false
% 3.59/1.00  --sat_fm_restart_options                ""
% 3.59/1.00  --sat_gr_def                            false
% 3.59/1.00  --sat_epr_types                         true
% 3.59/1.00  --sat_non_cyclic_types                  false
% 3.59/1.00  --sat_finite_models                     false
% 3.59/1.00  --sat_fm_lemmas                         false
% 3.59/1.00  --sat_fm_prep                           false
% 3.59/1.00  --sat_fm_uc_incr                        true
% 3.59/1.00  --sat_out_model                         small
% 3.59/1.00  --sat_out_clauses                       false
% 3.59/1.00  
% 3.59/1.00  ------ QBF Options
% 3.59/1.00  
% 3.59/1.00  --qbf_mode                              false
% 3.59/1.00  --qbf_elim_univ                         false
% 3.59/1.00  --qbf_dom_inst                          none
% 3.59/1.00  --qbf_dom_pre_inst                      false
% 3.59/1.00  --qbf_sk_in                             false
% 3.59/1.00  --qbf_pred_elim                         true
% 3.59/1.00  --qbf_split                             512
% 3.59/1.00  
% 3.59/1.00  ------ BMC1 Options
% 3.59/1.00  
% 3.59/1.00  --bmc1_incremental                      false
% 3.59/1.00  --bmc1_axioms                           reachable_all
% 3.59/1.00  --bmc1_min_bound                        0
% 3.59/1.00  --bmc1_max_bound                        -1
% 3.59/1.00  --bmc1_max_bound_default                -1
% 3.59/1.00  --bmc1_symbol_reachability              true
% 3.59/1.00  --bmc1_property_lemmas                  false
% 3.59/1.00  --bmc1_k_induction                      false
% 3.59/1.00  --bmc1_non_equiv_states                 false
% 3.59/1.00  --bmc1_deadlock                         false
% 3.59/1.00  --bmc1_ucm                              false
% 3.59/1.00  --bmc1_add_unsat_core                   none
% 3.59/1.00  --bmc1_unsat_core_children              false
% 3.59/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.00  --bmc1_out_stat                         full
% 3.59/1.00  --bmc1_ground_init                      false
% 3.59/1.00  --bmc1_pre_inst_next_state              false
% 3.59/1.00  --bmc1_pre_inst_state                   false
% 3.59/1.00  --bmc1_pre_inst_reach_state             false
% 3.59/1.00  --bmc1_out_unsat_core                   false
% 3.59/1.00  --bmc1_aig_witness_out                  false
% 3.59/1.00  --bmc1_verbose                          false
% 3.59/1.00  --bmc1_dump_clauses_tptp                false
% 3.59/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.00  --bmc1_dump_file                        -
% 3.59/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.00  --bmc1_ucm_extend_mode                  1
% 3.59/1.00  --bmc1_ucm_init_mode                    2
% 3.59/1.00  --bmc1_ucm_cone_mode                    none
% 3.59/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.00  --bmc1_ucm_relax_model                  4
% 3.59/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.00  --bmc1_ucm_layered_model                none
% 3.59/1.00  --bmc1_ucm_max_lemma_size               10
% 3.59/1.00  
% 3.59/1.00  ------ AIG Options
% 3.59/1.00  
% 3.59/1.00  --aig_mode                              false
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation Options
% 3.59/1.00  
% 3.59/1.00  --instantiation_flag                    true
% 3.59/1.00  --inst_sos_flag                         false
% 3.59/1.00  --inst_sos_phase                        true
% 3.59/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.00  --inst_lit_sel_side                     none
% 3.59/1.00  --inst_solver_per_active                1400
% 3.59/1.00  --inst_solver_calls_frac                1.
% 3.59/1.00  --inst_passive_queue_type               priority_queues
% 3.59/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.00  --inst_passive_queues_freq              [25;2]
% 3.59/1.00  --inst_dismatching                      true
% 3.59/1.00  --inst_eager_unprocessed_to_passive     true
% 3.59/1.00  --inst_prop_sim_given                   true
% 3.59/1.00  --inst_prop_sim_new                     false
% 3.59/1.00  --inst_subs_new                         false
% 3.59/1.00  --inst_eq_res_simp                      false
% 3.59/1.00  --inst_subs_given                       false
% 3.59/1.00  --inst_orphan_elimination               true
% 3.59/1.00  --inst_learning_loop_flag               true
% 3.59/1.00  --inst_learning_start                   3000
% 3.59/1.00  --inst_learning_factor                  2
% 3.59/1.00  --inst_start_prop_sim_after_learn       3
% 3.59/1.00  --inst_sel_renew                        solver
% 3.59/1.00  --inst_lit_activity_flag                true
% 3.59/1.00  --inst_restr_to_given                   false
% 3.59/1.00  --inst_activity_threshold               500
% 3.59/1.00  --inst_out_proof                        true
% 3.59/1.00  
% 3.59/1.00  ------ Resolution Options
% 3.59/1.00  
% 3.59/1.00  --resolution_flag                       false
% 3.59/1.00  --res_lit_sel                           adaptive
% 3.59/1.00  --res_lit_sel_side                      none
% 3.59/1.00  --res_ordering                          kbo
% 3.59/1.00  --res_to_prop_solver                    active
% 3.59/1.00  --res_prop_simpl_new                    false
% 3.59/1.00  --res_prop_simpl_given                  true
% 3.59/1.00  --res_passive_queue_type                priority_queues
% 3.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.00  --res_passive_queues_freq               [15;5]
% 3.59/1.00  --res_forward_subs                      full
% 3.59/1.00  --res_backward_subs                     full
% 3.59/1.00  --res_forward_subs_resolution           true
% 3.59/1.00  --res_backward_subs_resolution          true
% 3.59/1.00  --res_orphan_elimination                true
% 3.59/1.00  --res_time_limit                        2.
% 3.59/1.00  --res_out_proof                         true
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Options
% 3.59/1.00  
% 3.59/1.00  --superposition_flag                    true
% 3.59/1.00  --sup_passive_queue_type                priority_queues
% 3.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.59/1.00  --demod_completeness_check              fast
% 3.59/1.00  --demod_use_ground                      true
% 3.59/1.00  --sup_to_prop_solver                    passive
% 3.59/1.00  --sup_prop_simpl_new                    true
% 3.59/1.00  --sup_prop_simpl_given                  true
% 3.59/1.00  --sup_fun_splitting                     false
% 3.59/1.00  --sup_smt_interval                      50000
% 3.59/1.00  
% 3.59/1.00  ------ Superposition Simplification Setup
% 3.59/1.00  
% 3.59/1.00  --sup_indices_passive                   []
% 3.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_full_bw                           [BwDemod]
% 3.59/1.00  --sup_immed_triv                        [TrivRules]
% 3.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_immed_bw_main                     []
% 3.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.00  
% 3.59/1.00  ------ Combination Options
% 3.59/1.00  
% 3.59/1.00  --comb_res_mult                         3
% 3.59/1.00  --comb_sup_mult                         2
% 3.59/1.00  --comb_inst_mult                        10
% 3.59/1.00  
% 3.59/1.00  ------ Debug Options
% 3.59/1.00  
% 3.59/1.00  --dbg_backtrace                         false
% 3.59/1.00  --dbg_dump_prop_clauses                 false
% 3.59/1.00  --dbg_dump_prop_clauses_file            -
% 3.59/1.00  --dbg_out_stat                          false
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  ------ Proving...
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS status Theorem for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  fof(f14,conjecture,(
% 3.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f15,negated_conjecture,(
% 3.59/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 3.59/1.00    inference(negated_conjecture,[],[f14])).
% 3.59/1.00  
% 3.59/1.00  fof(f33,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : ((~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))) & m1_subset_1(X6,u1_struct_0(X2))) & (r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1))) & m1_subset_1(X5,u1_struct_0(X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f15])).
% 3.59/1.00  
% 3.59/1.00  fof(f34,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f33])).
% 3.59/1.00  
% 3.59/1.00  fof(f54,plain,(
% 3.59/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),sK9) & r2_hidden(sK9,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(sK9,u1_struct_0(X2)))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f53,plain,(
% 3.59/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),sK8))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,sK8) & v5_pre_topc(X3,X2,X1) & m1_subset_1(sK8,u1_struct_0(X1)))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f52,plain,(
% 3.59/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,sK7),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,sK7,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK7,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK7))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f51,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),sK6,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK6,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(sK6,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f50,plain,(
% 3.59/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,X0,k1_partfun1(u1_struct_0(sK5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK5),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(sK5))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,sK5,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f49,plain,(
% 3.59/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK4),X3,k6_domain_1(u1_struct_0(sK4),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(sK4,X0,X4,X5) & v5_pre_topc(X3,X2,sK4) & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK4)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK4)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f48,plain,(
% 3.59/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK3,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK3),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,sK3,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f55,plain,(
% 3.59/1.00    ((((((~r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) & r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) & m1_subset_1(sK9,u1_struct_0(sK5))) & r1_tmap_1(sK4,sK3,sK7,sK8) & v5_pre_topc(sK6,sK5,sK4) & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f34,f54,f53,f52,f51,f50,f49,f48])).
% 3.59/1.00  
% 3.59/1.00  fof(f94,plain,(
% 3.59/1.00    m1_subset_1(sK8,u1_struct_0(sK4))),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f9,axiom,(
% 3.59/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f23,plain,(
% 3.59/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f9])).
% 3.59/1.00  
% 3.59/1.00  fof(f24,plain,(
% 3.59/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.59/1.00    inference(flattening,[],[f23])).
% 3.59/1.00  
% 3.59/1.00  fof(f72,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f24])).
% 3.59/1.00  
% 3.59/1.00  fof(f2,axiom,(
% 3.59/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f60,plain,(
% 3.59/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f2])).
% 3.59/1.00  
% 3.59/1.00  fof(f104,plain,(
% 3.59/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.59/1.00    inference(definition_unfolding,[],[f72,f60])).
% 3.59/1.00  
% 3.59/1.00  fof(f11,axiom,(
% 3.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f27,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f11])).
% 3.59/1.00  
% 3.59/1.00  fof(f28,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f27])).
% 3.59/1.00  
% 3.59/1.00  fof(f74,plain,(
% 3.59/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f28])).
% 3.59/1.00  
% 3.59/1.00  fof(f10,axiom,(
% 3.59/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f25,plain,(
% 3.59/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f10])).
% 3.59/1.00  
% 3.59/1.00  fof(f26,plain,(
% 3.59/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f25])).
% 3.59/1.00  
% 3.59/1.00  fof(f73,plain,(
% 3.59/1.00    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f26])).
% 3.59/1.00  
% 3.59/1.00  fof(f3,axiom,(
% 3.59/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f16,plain,(
% 3.59/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.59/1.00    inference(ennf_transformation,[],[f3])).
% 3.59/1.00  
% 3.59/1.00  fof(f61,plain,(
% 3.59/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f16])).
% 3.59/1.00  
% 3.59/1.00  fof(f82,plain,(
% 3.59/1.00    ~v2_struct_0(sK4)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f83,plain,(
% 3.59/1.00    v2_pre_topc(sK4)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f84,plain,(
% 3.59/1.00    l1_pre_topc(sK4)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f90,plain,(
% 3.59/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f7,axiom,(
% 3.59/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f20,plain,(
% 3.59/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/1.00    inference(ennf_transformation,[],[f7])).
% 3.59/1.00  
% 3.59/1.00  fof(f70,plain,(
% 3.59/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f20])).
% 3.59/1.00  
% 3.59/1.00  fof(f98,plain,(
% 3.59/1.00    r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8)))),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f6,axiom,(
% 3.59/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f18,plain,(
% 3.59/1.00    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f6])).
% 3.59/1.00  
% 3.59/1.00  fof(f19,plain,(
% 3.59/1.00    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/1.00    inference(flattening,[],[f18])).
% 3.59/1.00  
% 3.59/1.00  fof(f39,plain,(
% 3.59/1.00    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/1.00    inference(nnf_transformation,[],[f19])).
% 3.59/1.00  
% 3.59/1.00  fof(f40,plain,(
% 3.59/1.00    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/1.00    inference(flattening,[],[f39])).
% 3.59/1.00  
% 3.59/1.00  fof(f41,plain,(
% 3.59/1.00    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/1.00    inference(rectify,[],[f40])).
% 3.59/1.00  
% 3.59/1.00  fof(f42,plain,(
% 3.59/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f43,plain,(
% 3.59/1.00    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) | ~r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK1(X0,X1,X2)),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.59/1.00  
% 3.59/1.00  fof(f65,plain,(
% 3.59/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f43])).
% 3.59/1.00  
% 3.59/1.00  fof(f109,plain,(
% 3.59/1.00    ( ! [X4,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/1.00    inference(equality_resolution,[],[f65])).
% 3.59/1.00  
% 3.59/1.00  fof(f88,plain,(
% 3.59/1.00    v1_funct_1(sK6)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f4,axiom,(
% 3.59/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f17,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.59/1.00    inference(ennf_transformation,[],[f4])).
% 3.59/1.00  
% 3.59/1.00  fof(f62,plain,(
% 3.59/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f17])).
% 3.59/1.00  
% 3.59/1.00  fof(f5,axiom,(
% 3.59/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f63,plain,(
% 3.59/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.59/1.00    inference(cnf_transformation,[],[f5])).
% 3.59/1.00  
% 3.59/1.00  fof(f1,axiom,(
% 3.59/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f35,plain,(
% 3.59/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.59/1.00    inference(nnf_transformation,[],[f1])).
% 3.59/1.00  
% 3.59/1.00  fof(f36,plain,(
% 3.59/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.59/1.00    inference(rectify,[],[f35])).
% 3.59/1.00  
% 3.59/1.00  fof(f37,plain,(
% 3.59/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f38,plain,(
% 3.59/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.59/1.00  
% 3.59/1.00  fof(f56,plain,(
% 3.59/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.59/1.00    inference(cnf_transformation,[],[f38])).
% 3.59/1.00  
% 3.59/1.00  fof(f103,plain,(
% 3.59/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 3.59/1.00    inference(definition_unfolding,[],[f56,f60])).
% 3.59/1.00  
% 3.59/1.00  fof(f107,plain,(
% 3.59/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 3.59/1.00    inference(equality_resolution,[],[f103])).
% 3.59/1.00  
% 3.59/1.00  fof(f97,plain,(
% 3.59/1.00    m1_subset_1(sK9,u1_struct_0(sK5))),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f8,axiom,(
% 3.59/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f21,plain,(
% 3.59/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f8])).
% 3.59/1.00  
% 3.59/1.00  fof(f22,plain,(
% 3.59/1.00    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.59/1.00    inference(flattening,[],[f21])).
% 3.59/1.00  
% 3.59/1.00  fof(f71,plain,(
% 3.59/1.00    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f22])).
% 3.59/1.00  
% 3.59/1.00  fof(f85,plain,(
% 3.59/1.00    ~v2_struct_0(sK5)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f86,plain,(
% 3.59/1.00    v2_pre_topc(sK5)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f87,plain,(
% 3.59/1.00    l1_pre_topc(sK5)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f89,plain,(
% 3.59/1.00    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f13,axiom,(
% 3.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f31,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f13])).
% 3.59/1.00  
% 3.59/1.00  fof(f32,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f31])).
% 3.59/1.00  
% 3.59/1.00  fof(f78,plain,(
% 3.59/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f32])).
% 3.59/1.00  
% 3.59/1.00  fof(f111,plain,(
% 3.59/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(equality_resolution,[],[f78])).
% 3.59/1.00  
% 3.59/1.00  fof(f99,plain,(
% 3.59/1.00    ~r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f79,plain,(
% 3.59/1.00    ~v2_struct_0(sK3)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f80,plain,(
% 3.59/1.00    v2_pre_topc(sK3)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f81,plain,(
% 3.59/1.00    l1_pre_topc(sK3)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f91,plain,(
% 3.59/1.00    v1_funct_1(sK7)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f92,plain,(
% 3.59/1.00    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f93,plain,(
% 3.59/1.00    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f12,axiom,(
% 3.59/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 3.59/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.00  
% 3.59/1.00  fof(f29,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.59/1.00    inference(ennf_transformation,[],[f12])).
% 3.59/1.00  
% 3.59/1.00  fof(f30,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(flattening,[],[f29])).
% 3.59/1.00  
% 3.59/1.00  fof(f44,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(nnf_transformation,[],[f30])).
% 3.59/1.00  
% 3.59/1.00  fof(f45,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(rectify,[],[f44])).
% 3.59/1.00  
% 3.59/1.00  fof(f46,plain,(
% 3.59/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.59/1.00    introduced(choice_axiom,[])).
% 3.59/1.00  
% 3.59/1.00  fof(f47,plain,(
% 3.59/1.00    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 3.59/1.00  
% 3.59/1.00  fof(f75,plain,(
% 3.59/1.00    ( ! [X4,X2,X0,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~v5_pre_topc(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.59/1.00    inference(cnf_transformation,[],[f47])).
% 3.59/1.00  
% 3.59/1.00  fof(f95,plain,(
% 3.59/1.00    v5_pre_topc(sK6,sK5,sK4)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  fof(f96,plain,(
% 3.59/1.00    r1_tmap_1(sK4,sK3,sK7,sK8)),
% 3.59/1.00    inference(cnf_transformation,[],[f55])).
% 3.59/1.00  
% 3.59/1.00  cnf(c_27,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1705,plain,
% 3.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_15,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,X1)
% 3.59/1.00      | v1_xboole_0(X1)
% 3.59/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1713,plain,
% 3.59/1.00      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 3.59/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.59/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3520,plain,
% 3.59/1.00      ( k6_domain_1(u1_struct_0(sK4),sK8) = k2_tarski(sK8,sK8)
% 3.59/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1705,c_1713]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_17,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.59/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 3.59/1.00      | v2_struct_0(X1)
% 3.59/1.00      | ~ v2_pre_topc(X1)
% 3.59/1.00      | ~ l1_pre_topc(X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1711,plain,
% 3.59/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.59/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0)) = iProver_top
% 3.59/1.00      | v2_struct_0(X1) = iProver_top
% 3.59/1.00      | v2_pre_topc(X1) != iProver_top
% 3.59/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_16,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.59/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.59/1.00      | v2_struct_0(X1)
% 3.59/1.00      | ~ v2_pre_topc(X1)
% 3.59/1.00      | ~ l1_pre_topc(X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1712,plain,
% 3.59/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.59/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.59/1.00      | v2_struct_0(X1) = iProver_top
% 3.59/1.00      | v2_pre_topc(X1) != iProver_top
% 3.59/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.59/1.00      | ~ r2_hidden(X2,X0)
% 3.59/1.00      | ~ v1_xboole_0(X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1724,plain,
% 3.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.59/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.59/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5201,plain,
% 3.59/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.59/1.00      | r2_hidden(X2,k1_connsp_2(X1,X0)) != iProver_top
% 3.59/1.00      | v2_struct_0(X1) = iProver_top
% 3.59/1.00      | v2_pre_topc(X1) != iProver_top
% 3.59/1.00      | l1_pre_topc(X1) != iProver_top
% 3.59/1.00      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1712,c_1724]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6560,plain,
% 3.59/1.00      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 3.59/1.00      | v2_struct_0(X1) = iProver_top
% 3.59/1.00      | v2_pre_topc(X1) != iProver_top
% 3.59/1.00      | l1_pre_topc(X1) != iProver_top
% 3.59/1.00      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1711,c_5201]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9017,plain,
% 3.59/1.00      ( v2_struct_0(sK4) = iProver_top
% 3.59/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.59/1.00      | l1_pre_topc(sK4) != iProver_top
% 3.59/1.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1705,c_6560]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_39,negated_conjecture,
% 3.59/1.00      ( ~ v2_struct_0(sK4) ),
% 3.59/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_46,plain,
% 3.59/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_38,negated_conjecture,
% 3.59/1.00      ( v2_pre_topc(sK4) ),
% 3.59/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_47,plain,
% 3.59/1.00      ( v2_pre_topc(sK4) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_37,negated_conjecture,
% 3.59/1.00      ( l1_pre_topc(sK4) ),
% 3.59/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_48,plain,
% 3.59/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_58,plain,
% 3.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2151,plain,
% 3.59/1.00      ( m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.59/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 3.59/1.00      | v2_struct_0(sK4)
% 3.59/1.00      | ~ v2_pre_topc(sK4)
% 3.59/1.00      | ~ l1_pre_topc(sK4) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2152,plain,
% 3.59/1.00      ( m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.59/1.00      | v2_struct_0(sK4) = iProver_top
% 3.59/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.59/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2151]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2157,plain,
% 3.59/1.00      ( ~ m1_subset_1(sK8,u1_struct_0(sK4))
% 3.59/1.00      | r2_hidden(sK8,k1_connsp_2(sK4,sK8))
% 3.59/1.00      | v2_struct_0(sK4)
% 3.59/1.00      | ~ v2_pre_topc(sK4)
% 3.59/1.00      | ~ l1_pre_topc(sK4) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2158,plain,
% 3.59/1.00      ( m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.59/1.00      | r2_hidden(sK8,k1_connsp_2(sK4,sK8)) = iProver_top
% 3.59/1.00      | v2_struct_0(sK4) = iProver_top
% 3.59/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.59/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2157]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2323,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.59/1.00      | ~ r2_hidden(X1,X0)
% 3.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3982,plain,
% 3.59/1.00      ( ~ m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.59/1.00      | ~ r2_hidden(X0,k1_connsp_2(sK4,sK8))
% 3.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_2323]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5192,plain,
% 3.59/1.00      ( ~ m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.59/1.00      | ~ r2_hidden(sK8,k1_connsp_2(sK4,sK8))
% 3.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_3982]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5193,plain,
% 3.59/1.00      ( m1_subset_1(k1_connsp_2(sK4,sK8),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.59/1.00      | r2_hidden(sK8,k1_connsp_2(sK4,sK8)) != iProver_top
% 3.59/1.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_5192]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9168,plain,
% 3.59/1.00      ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_9017,c_46,c_47,c_48,c_58,c_2152,c_2158,c_5193]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9173,plain,
% 3.59/1.00      ( k6_domain_1(u1_struct_0(sK4),sK8) = k2_tarski(sK8,sK8) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_3520,c_9168]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_31,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
% 3.59/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1701,plain,
% 3.59/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_13,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1715,plain,
% 3.59/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.59/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3100,plain,
% 3.59/1.00      ( k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k10_relat_1(sK6,X0) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1701,c_1715]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_23,negated_conjecture,
% 3.59/1.00      ( r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) ),
% 3.59/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1708,plain,
% 3.59/1.00      ( r2_hidden(sK9,k8_relset_1(u1_struct_0(sK5),u1_struct_0(sK4),sK6,k6_domain_1(u1_struct_0(sK4),sK8))) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3217,plain,
% 3.59/1.00      ( r2_hidden(sK9,k10_relat_1(sK6,k6_domain_1(u1_struct_0(sK4),sK8))) = iProver_top ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_3100,c_1708]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_11,plain,
% 3.59/1.00      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 3.59/1.00      | r2_hidden(k1_funct_1(X1,X0),X2)
% 3.59/1.00      | ~ v1_funct_1(X1)
% 3.59/1.00      | ~ v1_relat_1(X1) ),
% 3.59/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1717,plain,
% 3.59/1.00      ( r2_hidden(X0,k10_relat_1(X1,X2)) != iProver_top
% 3.59/1.00      | r2_hidden(k1_funct_1(X1,X0),X2) = iProver_top
% 3.59/1.00      | v1_funct_1(X1) != iProver_top
% 3.59/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5162,plain,
% 3.59/1.00      ( r2_hidden(k1_funct_1(sK6,sK9),k6_domain_1(u1_struct_0(sK4),sK8)) = iProver_top
% 3.59/1.00      | v1_funct_1(sK6) != iProver_top
% 3.59/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_3217,c_1717]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_33,negated_conjecture,
% 3.59/1.00      ( v1_funct_1(sK6) ),
% 3.59/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_52,plain,
% 3.59/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.59/1.00      | ~ v1_relat_1(X1)
% 3.59/1.00      | v1_relat_1(X0) ),
% 3.59/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1723,plain,
% 3.59/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.59/1.00      | v1_relat_1(X1) != iProver_top
% 3.59/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3018,plain,
% 3.59/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))) != iProver_top
% 3.59/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1701,c_1723]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6,plain,
% 3.59/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3032,plain,
% 3.59/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3033,plain,
% 3.59/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3032]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5525,plain,
% 3.59/1.00      ( r2_hidden(k1_funct_1(sK6,sK9),k6_domain_1(u1_struct_0(sK4),sK8)) = iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_5162,c_52,c_3018,c_3033]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9424,plain,
% 3.59/1.00      ( r2_hidden(k1_funct_1(sK6,sK9),k2_tarski(sK8,sK8)) = iProver_top ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_9173,c_5525]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3,plain,
% 3.59/1.00      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 3.59/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1725,plain,
% 3.59/1.00      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9594,plain,
% 3.59/1.00      ( k1_funct_1(sK6,sK9) = sK8 ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_9424,c_1725]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_24,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1707,plain,
% 3.59/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_14,plain,
% 3.59/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.59/1.00      | ~ m1_subset_1(X3,X1)
% 3.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/1.00      | ~ v1_funct_1(X0)
% 3.59/1.00      | v1_xboole_0(X1)
% 3.59/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1714,plain,
% 3.59/1.00      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 3.59/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.59/1.00      | m1_subset_1(X3,X0) != iProver_top
% 3.59/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/1.00      | v1_funct_1(X2) != iProver_top
% 3.59/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_6592,plain,
% 3.59/1.00      ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k1_funct_1(sK6,X0)
% 3.59/1.00      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.59/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.59/1.00      | v1_funct_1(sK6) != iProver_top
% 3.59/1.00      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1701,c_1714]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_36,negated_conjecture,
% 3.59/1.00      ( ~ v2_struct_0(sK5) ),
% 3.59/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_49,plain,
% 3.59/1.00      ( v2_struct_0(sK5) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_35,negated_conjecture,
% 3.59/1.00      ( v2_pre_topc(sK5) ),
% 3.59/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_50,plain,
% 3.59/1.00      ( v2_pre_topc(sK5) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_34,negated_conjecture,
% 3.59/1.00      ( l1_pre_topc(sK5) ),
% 3.59/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_51,plain,
% 3.59/1.00      ( l1_pre_topc(sK5) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_32,negated_conjecture,
% 3.59/1.00      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_53,plain,
% 3.59/1.00      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_61,plain,
% 3.59/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2148,plain,
% 3.59/1.00      ( m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.59/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK5))
% 3.59/1.00      | v2_struct_0(sK5)
% 3.59/1.00      | ~ v2_pre_topc(sK5)
% 3.59/1.00      | ~ l1_pre_topc(sK5) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2149,plain,
% 3.59/1.00      ( m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
% 3.59/1.00      | v2_struct_0(sK5) = iProver_top
% 3.59/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.59/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2148]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2154,plain,
% 3.59/1.00      ( ~ m1_subset_1(sK9,u1_struct_0(sK5))
% 3.59/1.00      | r2_hidden(sK9,k1_connsp_2(sK5,sK9))
% 3.59/1.00      | v2_struct_0(sK5)
% 3.59/1.00      | ~ v2_pre_topc(sK5)
% 3.59/1.00      | ~ l1_pre_topc(sK5) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2155,plain,
% 3.59/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
% 3.59/1.00      | r2_hidden(sK9,k1_connsp_2(sK5,sK9)) = iProver_top
% 3.59/1.00      | v2_struct_0(sK5) = iProver_top
% 3.59/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.59/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2154]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2318,plain,
% 3.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.59/1.00      | ~ r2_hidden(X1,X0)
% 3.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_3953,plain,
% 3.59/1.00      ( ~ m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.59/1.00      | ~ r2_hidden(X0,k1_connsp_2(sK5,sK9))
% 3.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_2318]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5189,plain,
% 3.59/1.00      ( ~ m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.59/1.00      | ~ r2_hidden(sK9,k1_connsp_2(sK5,sK9))
% 3.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_3953]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5190,plain,
% 3.59/1.00      ( m1_subset_1(k1_connsp_2(sK5,sK9),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.59/1.00      | r2_hidden(sK9,k1_connsp_2(sK5,sK9)) != iProver_top
% 3.59/1.00      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_5189]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_7674,plain,
% 3.59/1.00      ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,X0) = k1_funct_1(sK6,X0)
% 3.59/1.00      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_6592,c_49,c_50,c_51,c_52,c_53,c_61,c_2149,c_2155,
% 3.59/1.00                 c_5190]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_7682,plain,
% 3.59/1.00      ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9) = k1_funct_1(sK6,sK9) ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1707,c_7674]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_21,plain,
% 3.59/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.59/1.00      | ~ r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 3.59/1.00      | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3)
% 3.59/1.00      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 3.59/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.59/1.00      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1))
% 3.59/1.00      | v2_struct_0(X4)
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | v2_struct_0(X1)
% 3.59/1.00      | ~ v2_pre_topc(X4)
% 3.59/1.00      | ~ v2_pre_topc(X0)
% 3.59/1.00      | ~ v2_pre_topc(X1)
% 3.59/1.00      | ~ l1_pre_topc(X4)
% 3.59/1.00      | ~ l1_pre_topc(X0)
% 3.59/1.00      | ~ l1_pre_topc(X1)
% 3.59/1.00      | ~ v1_funct_1(X2)
% 3.59/1.00      | ~ v1_funct_1(X5) ),
% 3.59/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1710,plain,
% 3.59/1.00      ( r1_tmap_1(X0,X1,X2,X3) != iProver_top
% 3.59/1.00      | r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != iProver_top
% 3.59/1.00      | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3) = iProver_top
% 3.59/1.00      | v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)) != iProver_top
% 3.59/1.00      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.59/1.00      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.59/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) != iProver_top
% 3.59/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.59/1.00      | m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1)) != iProver_top
% 3.59/1.00      | v2_struct_0(X4) = iProver_top
% 3.59/1.00      | v2_struct_0(X0) = iProver_top
% 3.59/1.00      | v2_struct_0(X1) = iProver_top
% 3.59/1.00      | v2_pre_topc(X4) != iProver_top
% 3.59/1.00      | v2_pre_topc(X0) != iProver_top
% 3.59/1.00      | v2_pre_topc(X1) != iProver_top
% 3.59/1.00      | l1_pre_topc(X4) != iProver_top
% 3.59/1.00      | l1_pre_topc(X0) != iProver_top
% 3.59/1.00      | l1_pre_topc(X1) != iProver_top
% 3.59/1.00      | v1_funct_1(X2) != iProver_top
% 3.59/1.00      | v1_funct_1(X5) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_22,negated_conjecture,
% 3.59/1.00      ( ~ r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) ),
% 3.59/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_1709,plain,
% 3.59/1.00      ( r1_tmap_1(sK5,sK3,k1_partfun1(u1_struct_0(sK5),u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),sK6,sK7),sK9) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_4856,plain,
% 3.59/1.00      ( r1_tmap_1(sK4,sK3,sK7,k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9)) != iProver_top
% 3.59/1.00      | r1_tmap_1(sK5,sK4,sK6,sK9) != iProver_top
% 3.59/1.00      | v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.59/1.00      | v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) != iProver_top
% 3.59/1.00      | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9),u1_struct_0(sK4)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top
% 3.59/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.59/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) != iProver_top
% 3.59/1.00      | v2_struct_0(sK4) = iProver_top
% 3.59/1.00      | v2_struct_0(sK3) = iProver_top
% 3.59/1.00      | v2_struct_0(sK5) = iProver_top
% 3.59/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.59/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.59/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.59/1.00      | l1_pre_topc(sK4) != iProver_top
% 3.59/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.59/1.00      | l1_pre_topc(sK5) != iProver_top
% 3.59/1.00      | v1_funct_1(sK7) != iProver_top
% 3.59/1.00      | v1_funct_1(sK6) != iProver_top ),
% 3.59/1.00      inference(superposition,[status(thm)],[c_1710,c_1709]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_42,negated_conjecture,
% 3.59/1.00      ( ~ v2_struct_0(sK3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_43,plain,
% 3.59/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_41,negated_conjecture,
% 3.59/1.00      ( v2_pre_topc(sK3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_44,plain,
% 3.59/1.00      ( v2_pre_topc(sK3) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_40,negated_conjecture,
% 3.59/1.00      ( l1_pre_topc(sK3) ),
% 3.59/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_45,plain,
% 3.59/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_54,plain,
% 3.59/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_30,negated_conjecture,
% 3.59/1.00      ( v1_funct_1(sK7) ),
% 3.59/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_55,plain,
% 3.59/1.00      ( v1_funct_1(sK7) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_29,negated_conjecture,
% 3.59/1.00      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 3.59/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_56,plain,
% 3.59/1.00      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_28,negated_conjecture,
% 3.59/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.59/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_57,plain,
% 3.59/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_20,plain,
% 3.59/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.59/1.00      | ~ v5_pre_topc(X2,X0,X1)
% 3.59/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.59/1.00      | v2_struct_0(X1)
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | ~ v2_pre_topc(X1)
% 3.59/1.00      | ~ v2_pre_topc(X0)
% 3.59/1.00      | ~ l1_pre_topc(X1)
% 3.59/1.00      | ~ l1_pre_topc(X0)
% 3.59/1.00      | ~ v1_funct_1(X2) ),
% 3.59/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_26,negated_conjecture,
% 3.59/1.00      ( v5_pre_topc(sK6,sK5,sK4) ),
% 3.59/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_589,plain,
% 3.59/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.59/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.59/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.59/1.00      | v2_struct_0(X0)
% 3.59/1.00      | v2_struct_0(X1)
% 3.59/1.00      | ~ v2_pre_topc(X0)
% 3.59/1.00      | ~ v2_pre_topc(X1)
% 3.59/1.00      | ~ l1_pre_topc(X0)
% 3.59/1.00      | ~ l1_pre_topc(X1)
% 3.59/1.00      | ~ v1_funct_1(X2)
% 3.59/1.00      | sK6 != X2
% 3.59/1.00      | sK4 != X1
% 3.59/1.00      | sK5 != X0 ),
% 3.59/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_590,plain,
% 3.59/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0)
% 3.59/1.00      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
% 3.59/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.59/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.59/1.00      | v2_struct_0(sK4)
% 3.59/1.00      | v2_struct_0(sK5)
% 3.59/1.00      | ~ v2_pre_topc(sK4)
% 3.59/1.00      | ~ v2_pre_topc(sK5)
% 3.59/1.00      | ~ l1_pre_topc(sK4)
% 3.59/1.00      | ~ l1_pre_topc(sK5)
% 3.59/1.00      | ~ v1_funct_1(sK6) ),
% 3.59/1.00      inference(unflattening,[status(thm)],[c_589]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_594,plain,
% 3.59/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0) | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_590,c_39,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2094,plain,
% 3.59/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9)
% 3.59/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK5)) ),
% 3.59/1.00      inference(instantiation,[status(thm)],[c_594]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_2095,plain,
% 3.59/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9) = iProver_top
% 3.59/1.00      | m1_subset_1(sK9,u1_struct_0(sK5)) != iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_5250,plain,
% 3.59/1.00      ( r1_tmap_1(sK4,sK3,sK7,k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9)) != iProver_top
% 3.59/1.00      | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK4),sK6,sK9),u1_struct_0(sK4)) != iProver_top ),
% 3.59/1.00      inference(global_propositional_subsumption,
% 3.59/1.00                [status(thm)],
% 3.59/1.00                [c_4856,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_51,
% 3.59/1.00                 c_52,c_53,c_54,c_55,c_56,c_57,c_61,c_2095]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_7686,plain,
% 3.59/1.00      ( r1_tmap_1(sK4,sK3,sK7,k1_funct_1(sK6,sK9)) != iProver_top
% 3.59/1.00      | m1_subset_1(k1_funct_1(sK6,sK9),u1_struct_0(sK4)) != iProver_top ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_7682,c_5250]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_9761,plain,
% 3.59/1.00      ( r1_tmap_1(sK4,sK3,sK7,sK8) != iProver_top
% 3.59/1.00      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
% 3.59/1.00      inference(demodulation,[status(thm)],[c_9594,c_7686]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_25,negated_conjecture,
% 3.59/1.00      ( r1_tmap_1(sK4,sK3,sK7,sK8) ),
% 3.59/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(c_60,plain,
% 3.59/1.00      ( r1_tmap_1(sK4,sK3,sK7,sK8) = iProver_top ),
% 3.59/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.59/1.00  
% 3.59/1.00  cnf(contradiction,plain,
% 3.59/1.00      ( $false ),
% 3.59/1.00      inference(minisat,[status(thm)],[c_9761,c_60,c_58]) ).
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/1.00  
% 3.59/1.00  ------                               Statistics
% 3.59/1.00  
% 3.59/1.00  ------ General
% 3.59/1.00  
% 3.59/1.00  abstr_ref_over_cycles:                  0
% 3.59/1.00  abstr_ref_under_cycles:                 0
% 3.59/1.00  gc_basic_clause_elim:                   0
% 3.59/1.00  forced_gc_time:                         0
% 3.59/1.00  parsing_time:                           0.029
% 3.59/1.00  unif_index_cands_time:                  0.
% 3.59/1.00  unif_index_add_time:                    0.
% 3.59/1.00  orderings_time:                         0.
% 3.59/1.00  out_proof_time:                         0.011
% 3.59/1.00  total_time:                             0.463
% 3.59/1.00  num_of_symbols:                         64
% 3.59/1.00  num_of_terms:                           10931
% 3.59/1.00  
% 3.59/1.00  ------ Preprocessing
% 3.59/1.00  
% 3.59/1.00  num_of_splits:                          0
% 3.59/1.00  num_of_split_atoms:                     0
% 3.59/1.00  num_of_reused_defs:                     0
% 3.59/1.00  num_eq_ax_congr_red:                    57
% 3.59/1.00  num_of_sem_filtered_clauses:            1
% 3.59/1.00  num_of_subtypes:                        0
% 3.59/1.00  monotx_restored_types:                  0
% 3.59/1.00  sat_num_of_epr_types:                   0
% 3.59/1.00  sat_num_of_non_cyclic_types:            0
% 3.59/1.00  sat_guarded_non_collapsed_types:        0
% 3.59/1.00  num_pure_diseq_elim:                    0
% 3.59/1.00  simp_replaced_by:                       0
% 3.59/1.00  res_preprocessed:                       208
% 3.59/1.00  prep_upred:                             0
% 3.59/1.00  prep_unflattend:                        6
% 3.59/1.00  smt_new_axioms:                         0
% 3.59/1.00  pred_elim_cands:                        10
% 3.59/1.00  pred_elim:                              1
% 3.59/1.00  pred_elim_cl:                           1
% 3.59/1.00  pred_elim_cycles:                       4
% 3.59/1.00  merged_defs:                            0
% 3.59/1.00  merged_defs_ncl:                        0
% 3.59/1.00  bin_hyper_res:                          0
% 3.59/1.00  prep_cycles:                            4
% 3.59/1.00  pred_elim_time:                         0.036
% 3.59/1.00  splitting_time:                         0.
% 3.59/1.00  sem_filter_time:                        0.
% 3.59/1.00  monotx_time:                            0.001
% 3.59/1.00  subtype_inf_time:                       0.
% 3.59/1.00  
% 3.59/1.00  ------ Problem properties
% 3.59/1.00  
% 3.59/1.00  clauses:                                42
% 3.59/1.00  conjectures:                            20
% 3.59/1.00  epr:                                    12
% 3.59/1.00  horn:                                   32
% 3.59/1.00  ground:                                 20
% 3.59/1.00  unary:                                  22
% 3.59/1.00  binary:                                 3
% 3.59/1.00  lits:                                   132
% 3.59/1.00  lits_eq:                                11
% 3.59/1.00  fd_pure:                                0
% 3.59/1.00  fd_pseudo:                              0
% 3.59/1.00  fd_cond:                                0
% 3.59/1.00  fd_pseudo_cond:                         5
% 3.59/1.00  ac_symbols:                             0
% 3.59/1.00  
% 3.59/1.00  ------ Propositional Solver
% 3.59/1.00  
% 3.59/1.00  prop_solver_calls:                      27
% 3.59/1.00  prop_fast_solver_calls:                 1699
% 3.59/1.00  smt_solver_calls:                       0
% 3.59/1.00  smt_fast_solver_calls:                  0
% 3.59/1.00  prop_num_of_clauses:                    3836
% 3.59/1.00  prop_preprocess_simplified:             9520
% 3.59/1.00  prop_fo_subsumed:                       61
% 3.59/1.00  prop_solver_time:                       0.
% 3.59/1.00  smt_solver_time:                        0.
% 3.59/1.00  smt_fast_solver_time:                   0.
% 3.59/1.00  prop_fast_solver_time:                  0.
% 3.59/1.00  prop_unsat_core_time:                   0.
% 3.59/1.00  
% 3.59/1.00  ------ QBF
% 3.59/1.00  
% 3.59/1.00  qbf_q_res:                              0
% 3.59/1.00  qbf_num_tautologies:                    0
% 3.59/1.00  qbf_prep_cycles:                        0
% 3.59/1.00  
% 3.59/1.00  ------ BMC1
% 3.59/1.00  
% 3.59/1.00  bmc1_current_bound:                     -1
% 3.59/1.00  bmc1_last_solved_bound:                 -1
% 3.59/1.00  bmc1_unsat_core_size:                   -1
% 3.59/1.00  bmc1_unsat_core_parents_size:           -1
% 3.59/1.00  bmc1_merge_next_fun:                    0
% 3.59/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.59/1.00  
% 3.59/1.00  ------ Instantiation
% 3.59/1.00  
% 3.59/1.00  inst_num_of_clauses:                    996
% 3.59/1.00  inst_num_in_passive:                    114
% 3.59/1.00  inst_num_in_active:                     398
% 3.59/1.00  inst_num_in_unprocessed:                484
% 3.59/1.00  inst_num_of_loops:                      440
% 3.59/1.00  inst_num_of_learning_restarts:          0
% 3.59/1.00  inst_num_moves_active_passive:          40
% 3.59/1.00  inst_lit_activity:                      0
% 3.59/1.00  inst_lit_activity_moves:                0
% 3.59/1.00  inst_num_tautologies:                   0
% 3.59/1.00  inst_num_prop_implied:                  0
% 3.59/1.00  inst_num_existing_simplified:           0
% 3.59/1.00  inst_num_eq_res_simplified:             0
% 3.59/1.00  inst_num_child_elim:                    0
% 3.59/1.00  inst_num_of_dismatching_blockings:      24
% 3.59/1.00  inst_num_of_non_proper_insts:           689
% 3.59/1.00  inst_num_of_duplicates:                 0
% 3.59/1.00  inst_inst_num_from_inst_to_res:         0
% 3.59/1.00  inst_dismatching_checking_time:         0.
% 3.59/1.00  
% 3.59/1.00  ------ Resolution
% 3.59/1.00  
% 3.59/1.00  res_num_of_clauses:                     0
% 3.59/1.00  res_num_in_passive:                     0
% 3.59/1.00  res_num_in_active:                      0
% 3.59/1.00  res_num_of_loops:                       212
% 3.59/1.00  res_forward_subset_subsumed:            25
% 3.59/1.00  res_backward_subset_subsumed:           0
% 3.59/1.00  res_forward_subsumed:                   0
% 3.59/1.00  res_backward_subsumed:                  0
% 3.59/1.00  res_forward_subsumption_resolution:     0
% 3.59/1.00  res_backward_subsumption_resolution:    0
% 3.59/1.00  res_clause_to_clause_subsumption:       613
% 3.59/1.00  res_orphan_elimination:                 0
% 3.59/1.00  res_tautology_del:                      27
% 3.59/1.00  res_num_eq_res_simplified:              0
% 3.59/1.00  res_num_sel_changes:                    0
% 3.59/1.00  res_moves_from_active_to_pass:          0
% 3.59/1.00  
% 3.59/1.00  ------ Superposition
% 3.59/1.00  
% 3.59/1.00  sup_time_total:                         0.
% 3.59/1.00  sup_time_generating:                    0.
% 3.59/1.00  sup_time_sim_full:                      0.
% 3.59/1.00  sup_time_sim_immed:                     0.
% 3.59/1.00  
% 3.59/1.00  sup_num_of_clauses:                     136
% 3.59/1.00  sup_num_in_active:                      71
% 3.59/1.00  sup_num_in_passive:                     65
% 3.59/1.00  sup_num_of_loops:                       86
% 3.59/1.00  sup_fw_superposition:                   77
% 3.59/1.00  sup_bw_superposition:                   67
% 3.59/1.00  sup_immediate_simplified:               21
% 3.59/1.00  sup_given_eliminated:                   2
% 3.59/1.00  comparisons_done:                       0
% 3.59/1.00  comparisons_avoided:                    7
% 3.59/1.00  
% 3.59/1.00  ------ Simplifications
% 3.59/1.00  
% 3.59/1.00  
% 3.59/1.00  sim_fw_subset_subsumed:                 8
% 3.59/1.00  sim_bw_subset_subsumed:                 2
% 3.59/1.00  sim_fw_subsumed:                        14
% 3.59/1.00  sim_bw_subsumed:                        1
% 3.59/1.00  sim_fw_subsumption_res:                 1
% 3.59/1.00  sim_bw_subsumption_res:                 0
% 3.59/1.00  sim_tautology_del:                      4
% 3.59/1.00  sim_eq_tautology_del:                   1
% 3.59/1.00  sim_eq_res_simp:                        1
% 3.59/1.00  sim_fw_demodulated:                     0
% 3.59/1.00  sim_bw_demodulated:                     12
% 3.59/1.00  sim_light_normalised:                   0
% 3.59/1.00  sim_joinable_taut:                      0
% 3.59/1.00  sim_joinable_simp:                      0
% 3.59/1.00  sim_ac_normalised:                      0
% 3.59/1.00  sim_smt_subsumption:                    0
% 3.59/1.00  
%------------------------------------------------------------------------------
