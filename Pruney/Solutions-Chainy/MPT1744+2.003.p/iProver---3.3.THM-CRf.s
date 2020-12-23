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
% DateTime   : Thu Dec  3 12:22:17 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  197 (1013 expanded)
%              Number of clauses        :  105 ( 183 expanded)
%              Number of leaves         :   23 ( 475 expanded)
%              Depth                    :   19
%              Number of atoms          : 1042 (16342 expanded)
%              Number of equality atoms :  253 ( 303 expanded)
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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
          & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),sK8)
        & r2_hidden(sK8,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
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
            & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),sK7)))
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & r1_tmap_1(X1,X0,X4,sK7)
        & v5_pre_topc(X3,X2,X1)
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
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
                ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,sK6),X6)
                & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & r1_tmap_1(X1,X0,sK6,X5)
            & v5_pre_topc(X3,X2,X1)
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK6,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK6) ) ) ),
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
                    ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),sK5,X4),X6)
                    & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK5,k6_domain_1(u1_struct_0(X1),X5)))
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & r1_tmap_1(X1,X0,X4,X5)
                & v5_pre_topc(sK5,X2,X1)
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
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
                        ( ~ r1_tmap_1(sK4,X0,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                        & r2_hidden(X6,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                        & m1_subset_1(X6,u1_struct_0(sK4)) )
                    & r1_tmap_1(X1,X0,X4,X5)
                    & v5_pre_topc(X3,sK4,X1)
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
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
                            ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(X0),X3,X4),X6)
                            & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK3),X3,k6_domain_1(u1_struct_0(sK3),X5)))
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & r1_tmap_1(sK3,X0,X4,X5)
                        & v5_pre_topc(X3,X2,sK3)
                        & m1_subset_1(X5,u1_struct_0(sK3)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK3))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
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
                              ( ~ r1_tmap_1(X2,sK2,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK2),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,sK2,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK2))
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
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ~ r1_tmap_1(sK4,sK2,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK6),sK8)
    & r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k6_domain_1(u1_struct_0(sK3),sK7)))
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & r1_tmap_1(sK3,sK2,sK6,sK7)
    & v5_pre_topc(sK5,sK4,sK3)
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f35,f54,f53,f52,f51,f50,f49,f48])).

fof(f95,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k6_domain_1(u1_struct_0(sK3),sK7))) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
          <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            | ~ r2_hidden(k1_funct_1(X3,X4),X2)
            | ~ r2_hidden(X4,X0) )
          & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            | ~ r2_hidden(k1_funct_1(X3,X4),X2)
            | ~ r2_hidden(X4,X0) )
          & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X4),X2)
      | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f57])).

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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f100,plain,(
    ~ r1_tmap_1(sK4,sK2,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK6),sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f98,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

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
     => ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2))
                    & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f76,plain,(
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

fof(f96,plain,(
    v5_pre_topc(sK5,sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f97,plain,(
    r1_tmap_1(sK3,sK2,sK6,sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1510,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1516,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3389,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK7) = k1_tarski(sK7)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_1516])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_18,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_82,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_85,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1910,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK7) = k1_tarski(sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3645,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK7) = k1_tarski(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3389,c_41,c_39,c_29,c_82,c_85,c_1910])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k6_domain_1(u1_struct_0(sK3),sK7))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1513,plain,
    ( r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k6_domain_1(u1_struct_0(sK3),sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3648,plain,
    ( r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k1_tarski(sK7))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3645,c_1513])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k8_relset_1(X1,X2,X0,X4))
    | r2_hidden(k1_funct_1(X0,X3),X4)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1518,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,k8_relset_1(X2,X0,X1,X4)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X4) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4371,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK8),k1_tarski(sK7)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3648,c_1518])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_54,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_55,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_56,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5070,plain,
    ( r2_hidden(k1_funct_1(sK5,sK8),k1_tarski(sK7)) = iProver_top
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4371,c_54,c_55,c_56])).

cnf(c_5071,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK5,sK8),k1_tarski(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5070])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1524,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5076,plain,
    ( k1_funct_1(sK5,sK8) = sK7
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5071,c_1524])).

cnf(c_23,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
    | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1515,plain,
    ( r1_tmap_1(X0,X1,X2,X3) != iProver_top
    | r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != iProver_top
    | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3) = iProver_top
    | v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1)) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X4) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK2,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK6),sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1514,plain,
    ( r1_tmap_1(sK4,sK2,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK6),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4975,plain,
    ( r1_tmap_1(sK3,sK2,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK8)) != iProver_top
    | r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK8),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_1514])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1512,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1506,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1520,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4033,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_1520])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_51,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_53,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_428,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_17,c_18])).

cnf(c_2090,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_428])).

cnf(c_2091,plain,
    ( v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2090])).

cnf(c_4852,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4033,c_51,c_53,c_54,c_55,c_2091])).

cnf(c_4861,plain,
    ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK8) = k1_funct_1(sK5,sK8) ),
    inference(superposition,[status(thm)],[c_1512,c_4852])).

cnf(c_4976,plain,
    ( r1_tmap_1(sK3,sK2,sK6,k1_funct_1(sK5,sK8)) != iProver_top
    | r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_funct_1(sK5,sK8),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4975,c_4861])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_45,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_46,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_47,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_49,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_50,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_52,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_57,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_58,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_59,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_63,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v5_pre_topc(X2,X0,X1)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( v5_pre_topc(sK5,sK4,sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_529,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | sK5 != X2
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_530,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_534,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

cnf(c_1876,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_1877,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1876])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1521,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4880,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k1_funct_1(sK5,sK8),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4861,c_1521])).

cnf(c_6472,plain,
    ( r1_tmap_1(sK3,sK2,sK6,k1_funct_1(sK5,sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4976,c_45,c_46,c_47,c_48,c_49,c_50,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_63,c_1877,c_2091,c_4880])).

cnf(c_6480,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | r1_tmap_1(sK3,sK2,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5076,c_6472])).

cnf(c_27,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK6,sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_62,plain,
    ( r1_tmap_1(sK3,sK2,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6539,plain,
    ( u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6480,c_62])).

cnf(c_1509,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1523,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3154,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1523])).

cnf(c_6563,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6539,c_3154])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6586,plain,
    ( v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6563,c_6])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1522,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3510,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1509,c_1522])).

cnf(c_81,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_83,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_84,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_86,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_3734,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3510,c_48,c_50,c_57,c_58,c_83,c_86])).

cnf(c_1494,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_3740,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3734,c_1494])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_121,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6586,c_3740,c_121,c_47,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:32:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.21/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/0.99  
% 3.21/0.99  ------  iProver source info
% 3.21/0.99  
% 3.21/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.21/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/0.99  git: non_committed_changes: false
% 3.21/0.99  git: last_make_outside_of_git: false
% 3.21/0.99  
% 3.21/0.99  ------ 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options
% 3.21/0.99  
% 3.21/0.99  --out_options                           all
% 3.21/0.99  --tptp_safe_out                         true
% 3.21/0.99  --problem_path                          ""
% 3.21/0.99  --include_path                          ""
% 3.21/0.99  --clausifier                            res/vclausify_rel
% 3.21/0.99  --clausifier_options                    --mode clausify
% 3.21/0.99  --stdin                                 false
% 3.21/0.99  --stats_out                             all
% 3.21/0.99  
% 3.21/0.99  ------ General Options
% 3.21/0.99  
% 3.21/0.99  --fof                                   false
% 3.21/0.99  --time_out_real                         305.
% 3.21/0.99  --time_out_virtual                      -1.
% 3.21/0.99  --symbol_type_check                     false
% 3.21/0.99  --clausify_out                          false
% 3.21/0.99  --sig_cnt_out                           false
% 3.21/0.99  --trig_cnt_out                          false
% 3.21/0.99  --trig_cnt_out_tolerance                1.
% 3.21/0.99  --trig_cnt_out_sk_spl                   false
% 3.21/0.99  --abstr_cl_out                          false
% 3.21/0.99  
% 3.21/0.99  ------ Global Options
% 3.21/0.99  
% 3.21/0.99  --schedule                              default
% 3.21/0.99  --add_important_lit                     false
% 3.21/0.99  --prop_solver_per_cl                    1000
% 3.21/0.99  --min_unsat_core                        false
% 3.21/0.99  --soft_assumptions                      false
% 3.21/0.99  --soft_lemma_size                       3
% 3.21/0.99  --prop_impl_unit_size                   0
% 3.21/0.99  --prop_impl_unit                        []
% 3.21/0.99  --share_sel_clauses                     true
% 3.21/0.99  --reset_solvers                         false
% 3.21/0.99  --bc_imp_inh                            [conj_cone]
% 3.21/0.99  --conj_cone_tolerance                   3.
% 3.21/0.99  --extra_neg_conj                        none
% 3.21/0.99  --large_theory_mode                     true
% 3.21/0.99  --prolific_symb_bound                   200
% 3.21/0.99  --lt_threshold                          2000
% 3.21/0.99  --clause_weak_htbl                      true
% 3.21/0.99  --gc_record_bc_elim                     false
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing Options
% 3.21/0.99  
% 3.21/0.99  --preprocessing_flag                    true
% 3.21/0.99  --time_out_prep_mult                    0.1
% 3.21/0.99  --splitting_mode                        input
% 3.21/0.99  --splitting_grd                         true
% 3.21/0.99  --splitting_cvd                         false
% 3.21/0.99  --splitting_cvd_svl                     false
% 3.21/0.99  --splitting_nvd                         32
% 3.21/0.99  --sub_typing                            true
% 3.21/0.99  --prep_gs_sim                           true
% 3.21/0.99  --prep_unflatten                        true
% 3.21/0.99  --prep_res_sim                          true
% 3.21/0.99  --prep_upred                            true
% 3.21/0.99  --prep_sem_filter                       exhaustive
% 3.21/0.99  --prep_sem_filter_out                   false
% 3.21/0.99  --pred_elim                             true
% 3.21/0.99  --res_sim_input                         true
% 3.21/0.99  --eq_ax_congr_red                       true
% 3.21/0.99  --pure_diseq_elim                       true
% 3.21/0.99  --brand_transform                       false
% 3.21/0.99  --non_eq_to_eq                          false
% 3.21/0.99  --prep_def_merge                        true
% 3.21/0.99  --prep_def_merge_prop_impl              false
% 3.21/0.99  --prep_def_merge_mbd                    true
% 3.21/0.99  --prep_def_merge_tr_red                 false
% 3.21/0.99  --prep_def_merge_tr_cl                  false
% 3.21/0.99  --smt_preprocessing                     true
% 3.21/0.99  --smt_ac_axioms                         fast
% 3.21/0.99  --preprocessed_out                      false
% 3.21/0.99  --preprocessed_stats                    false
% 3.21/0.99  
% 3.21/0.99  ------ Abstraction refinement Options
% 3.21/0.99  
% 3.21/0.99  --abstr_ref                             []
% 3.21/0.99  --abstr_ref_prep                        false
% 3.21/0.99  --abstr_ref_until_sat                   false
% 3.21/0.99  --abstr_ref_sig_restrict                funpre
% 3.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/0.99  --abstr_ref_under                       []
% 3.21/0.99  
% 3.21/0.99  ------ SAT Options
% 3.21/0.99  
% 3.21/0.99  --sat_mode                              false
% 3.21/0.99  --sat_fm_restart_options                ""
% 3.21/0.99  --sat_gr_def                            false
% 3.21/0.99  --sat_epr_types                         true
% 3.21/0.99  --sat_non_cyclic_types                  false
% 3.21/0.99  --sat_finite_models                     false
% 3.21/0.99  --sat_fm_lemmas                         false
% 3.21/0.99  --sat_fm_prep                           false
% 3.21/0.99  --sat_fm_uc_incr                        true
% 3.21/0.99  --sat_out_model                         small
% 3.21/0.99  --sat_out_clauses                       false
% 3.21/0.99  
% 3.21/0.99  ------ QBF Options
% 3.21/0.99  
% 3.21/0.99  --qbf_mode                              false
% 3.21/0.99  --qbf_elim_univ                         false
% 3.21/0.99  --qbf_dom_inst                          none
% 3.21/0.99  --qbf_dom_pre_inst                      false
% 3.21/0.99  --qbf_sk_in                             false
% 3.21/0.99  --qbf_pred_elim                         true
% 3.21/0.99  --qbf_split                             512
% 3.21/0.99  
% 3.21/0.99  ------ BMC1 Options
% 3.21/0.99  
% 3.21/0.99  --bmc1_incremental                      false
% 3.21/0.99  --bmc1_axioms                           reachable_all
% 3.21/0.99  --bmc1_min_bound                        0
% 3.21/0.99  --bmc1_max_bound                        -1
% 3.21/0.99  --bmc1_max_bound_default                -1
% 3.21/0.99  --bmc1_symbol_reachability              true
% 3.21/0.99  --bmc1_property_lemmas                  false
% 3.21/0.99  --bmc1_k_induction                      false
% 3.21/0.99  --bmc1_non_equiv_states                 false
% 3.21/0.99  --bmc1_deadlock                         false
% 3.21/0.99  --bmc1_ucm                              false
% 3.21/0.99  --bmc1_add_unsat_core                   none
% 3.21/0.99  --bmc1_unsat_core_children              false
% 3.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/0.99  --bmc1_out_stat                         full
% 3.21/0.99  --bmc1_ground_init                      false
% 3.21/0.99  --bmc1_pre_inst_next_state              false
% 3.21/0.99  --bmc1_pre_inst_state                   false
% 3.21/0.99  --bmc1_pre_inst_reach_state             false
% 3.21/0.99  --bmc1_out_unsat_core                   false
% 3.21/0.99  --bmc1_aig_witness_out                  false
% 3.21/0.99  --bmc1_verbose                          false
% 3.21/0.99  --bmc1_dump_clauses_tptp                false
% 3.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.21/0.99  --bmc1_dump_file                        -
% 3.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.21/0.99  --bmc1_ucm_extend_mode                  1
% 3.21/0.99  --bmc1_ucm_init_mode                    2
% 3.21/0.99  --bmc1_ucm_cone_mode                    none
% 3.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.21/0.99  --bmc1_ucm_relax_model                  4
% 3.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/0.99  --bmc1_ucm_layered_model                none
% 3.21/0.99  --bmc1_ucm_max_lemma_size               10
% 3.21/0.99  
% 3.21/0.99  ------ AIG Options
% 3.21/0.99  
% 3.21/0.99  --aig_mode                              false
% 3.21/0.99  
% 3.21/0.99  ------ Instantiation Options
% 3.21/0.99  
% 3.21/0.99  --instantiation_flag                    true
% 3.21/0.99  --inst_sos_flag                         false
% 3.21/0.99  --inst_sos_phase                        true
% 3.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel_side                     num_symb
% 3.21/0.99  --inst_solver_per_active                1400
% 3.21/0.99  --inst_solver_calls_frac                1.
% 3.21/0.99  --inst_passive_queue_type               priority_queues
% 3.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/0.99  --inst_passive_queues_freq              [25;2]
% 3.21/0.99  --inst_dismatching                      true
% 3.21/0.99  --inst_eager_unprocessed_to_passive     true
% 3.21/0.99  --inst_prop_sim_given                   true
% 3.21/0.99  --inst_prop_sim_new                     false
% 3.21/0.99  --inst_subs_new                         false
% 3.21/0.99  --inst_eq_res_simp                      false
% 3.21/0.99  --inst_subs_given                       false
% 3.21/0.99  --inst_orphan_elimination               true
% 3.21/0.99  --inst_learning_loop_flag               true
% 3.21/0.99  --inst_learning_start                   3000
% 3.21/0.99  --inst_learning_factor                  2
% 3.21/0.99  --inst_start_prop_sim_after_learn       3
% 3.21/0.99  --inst_sel_renew                        solver
% 3.21/0.99  --inst_lit_activity_flag                true
% 3.21/0.99  --inst_restr_to_given                   false
% 3.21/0.99  --inst_activity_threshold               500
% 3.21/0.99  --inst_out_proof                        true
% 3.21/0.99  
% 3.21/0.99  ------ Resolution Options
% 3.21/0.99  
% 3.21/0.99  --resolution_flag                       true
% 3.21/0.99  --res_lit_sel                           adaptive
% 3.21/0.99  --res_lit_sel_side                      none
% 3.21/0.99  --res_ordering                          kbo
% 3.21/0.99  --res_to_prop_solver                    active
% 3.21/0.99  --res_prop_simpl_new                    false
% 3.21/0.99  --res_prop_simpl_given                  true
% 3.21/0.99  --res_passive_queue_type                priority_queues
% 3.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/0.99  --res_passive_queues_freq               [15;5]
% 3.21/0.99  --res_forward_subs                      full
% 3.21/0.99  --res_backward_subs                     full
% 3.21/0.99  --res_forward_subs_resolution           true
% 3.21/0.99  --res_backward_subs_resolution          true
% 3.21/0.99  --res_orphan_elimination                true
% 3.21/0.99  --res_time_limit                        2.
% 3.21/0.99  --res_out_proof                         true
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Options
% 3.21/0.99  
% 3.21/0.99  --superposition_flag                    true
% 3.21/0.99  --sup_passive_queue_type                priority_queues
% 3.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.21/0.99  --demod_completeness_check              fast
% 3.21/0.99  --demod_use_ground                      true
% 3.21/0.99  --sup_to_prop_solver                    passive
% 3.21/0.99  --sup_prop_simpl_new                    true
% 3.21/0.99  --sup_prop_simpl_given                  true
% 3.21/0.99  --sup_fun_splitting                     false
% 3.21/0.99  --sup_smt_interval                      50000
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Simplification Setup
% 3.21/0.99  
% 3.21/0.99  --sup_indices_passive                   []
% 3.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_full_bw                           [BwDemod]
% 3.21/0.99  --sup_immed_triv                        [TrivRules]
% 3.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_immed_bw_main                     []
% 3.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  
% 3.21/0.99  ------ Combination Options
% 3.21/0.99  
% 3.21/0.99  --comb_res_mult                         3
% 3.21/0.99  --comb_sup_mult                         2
% 3.21/0.99  --comb_inst_mult                        10
% 3.21/0.99  
% 3.21/0.99  ------ Debug Options
% 3.21/0.99  
% 3.21/0.99  --dbg_backtrace                         false
% 3.21/0.99  --dbg_dump_prop_clauses                 false
% 3.21/0.99  --dbg_dump_prop_clauses_file            -
% 3.21/0.99  --dbg_out_stat                          false
% 3.21/0.99  ------ Parsing...
% 3.21/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/0.99  ------ Proving...
% 3.21/0.99  ------ Problem Properties 
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  clauses                                 41
% 3.21/0.99  conjectures                             20
% 3.21/0.99  EPR                                     13
% 3.21/0.99  Horn                                    29
% 3.21/0.99  unary                                   24
% 3.21/0.99  binary                                  2
% 3.21/0.99  lits                                    127
% 3.21/0.99  lits eq                                 15
% 3.21/0.99  fd_pure                                 0
% 3.21/0.99  fd_pseudo                               0
% 3.21/0.99  fd_cond                                 4
% 3.21/0.99  fd_pseudo_cond                          2
% 3.21/0.99  AC symbols                              0
% 3.21/0.99  
% 3.21/0.99  ------ Schedule dynamic 5 is on 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  ------ 
% 3.21/0.99  Current options:
% 3.21/0.99  ------ 
% 3.21/0.99  
% 3.21/0.99  ------ Input Options
% 3.21/0.99  
% 3.21/0.99  --out_options                           all
% 3.21/0.99  --tptp_safe_out                         true
% 3.21/0.99  --problem_path                          ""
% 3.21/0.99  --include_path                          ""
% 3.21/0.99  --clausifier                            res/vclausify_rel
% 3.21/0.99  --clausifier_options                    --mode clausify
% 3.21/0.99  --stdin                                 false
% 3.21/0.99  --stats_out                             all
% 3.21/0.99  
% 3.21/0.99  ------ General Options
% 3.21/0.99  
% 3.21/0.99  --fof                                   false
% 3.21/0.99  --time_out_real                         305.
% 3.21/0.99  --time_out_virtual                      -1.
% 3.21/0.99  --symbol_type_check                     false
% 3.21/0.99  --clausify_out                          false
% 3.21/0.99  --sig_cnt_out                           false
% 3.21/0.99  --trig_cnt_out                          false
% 3.21/0.99  --trig_cnt_out_tolerance                1.
% 3.21/0.99  --trig_cnt_out_sk_spl                   false
% 3.21/0.99  --abstr_cl_out                          false
% 3.21/0.99  
% 3.21/0.99  ------ Global Options
% 3.21/0.99  
% 3.21/0.99  --schedule                              default
% 3.21/0.99  --add_important_lit                     false
% 3.21/0.99  --prop_solver_per_cl                    1000
% 3.21/0.99  --min_unsat_core                        false
% 3.21/0.99  --soft_assumptions                      false
% 3.21/0.99  --soft_lemma_size                       3
% 3.21/0.99  --prop_impl_unit_size                   0
% 3.21/0.99  --prop_impl_unit                        []
% 3.21/0.99  --share_sel_clauses                     true
% 3.21/0.99  --reset_solvers                         false
% 3.21/0.99  --bc_imp_inh                            [conj_cone]
% 3.21/0.99  --conj_cone_tolerance                   3.
% 3.21/0.99  --extra_neg_conj                        none
% 3.21/0.99  --large_theory_mode                     true
% 3.21/0.99  --prolific_symb_bound                   200
% 3.21/0.99  --lt_threshold                          2000
% 3.21/0.99  --clause_weak_htbl                      true
% 3.21/0.99  --gc_record_bc_elim                     false
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing Options
% 3.21/0.99  
% 3.21/0.99  --preprocessing_flag                    true
% 3.21/0.99  --time_out_prep_mult                    0.1
% 3.21/0.99  --splitting_mode                        input
% 3.21/0.99  --splitting_grd                         true
% 3.21/0.99  --splitting_cvd                         false
% 3.21/0.99  --splitting_cvd_svl                     false
% 3.21/0.99  --splitting_nvd                         32
% 3.21/0.99  --sub_typing                            true
% 3.21/0.99  --prep_gs_sim                           true
% 3.21/0.99  --prep_unflatten                        true
% 3.21/0.99  --prep_res_sim                          true
% 3.21/0.99  --prep_upred                            true
% 3.21/0.99  --prep_sem_filter                       exhaustive
% 3.21/0.99  --prep_sem_filter_out                   false
% 3.21/0.99  --pred_elim                             true
% 3.21/0.99  --res_sim_input                         true
% 3.21/0.99  --eq_ax_congr_red                       true
% 3.21/0.99  --pure_diseq_elim                       true
% 3.21/0.99  --brand_transform                       false
% 3.21/0.99  --non_eq_to_eq                          false
% 3.21/0.99  --prep_def_merge                        true
% 3.21/0.99  --prep_def_merge_prop_impl              false
% 3.21/0.99  --prep_def_merge_mbd                    true
% 3.21/0.99  --prep_def_merge_tr_red                 false
% 3.21/0.99  --prep_def_merge_tr_cl                  false
% 3.21/0.99  --smt_preprocessing                     true
% 3.21/0.99  --smt_ac_axioms                         fast
% 3.21/0.99  --preprocessed_out                      false
% 3.21/0.99  --preprocessed_stats                    false
% 3.21/0.99  
% 3.21/0.99  ------ Abstraction refinement Options
% 3.21/0.99  
% 3.21/0.99  --abstr_ref                             []
% 3.21/0.99  --abstr_ref_prep                        false
% 3.21/0.99  --abstr_ref_until_sat                   false
% 3.21/0.99  --abstr_ref_sig_restrict                funpre
% 3.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/0.99  --abstr_ref_under                       []
% 3.21/0.99  
% 3.21/0.99  ------ SAT Options
% 3.21/0.99  
% 3.21/0.99  --sat_mode                              false
% 3.21/0.99  --sat_fm_restart_options                ""
% 3.21/0.99  --sat_gr_def                            false
% 3.21/0.99  --sat_epr_types                         true
% 3.21/0.99  --sat_non_cyclic_types                  false
% 3.21/0.99  --sat_finite_models                     false
% 3.21/0.99  --sat_fm_lemmas                         false
% 3.21/0.99  --sat_fm_prep                           false
% 3.21/0.99  --sat_fm_uc_incr                        true
% 3.21/0.99  --sat_out_model                         small
% 3.21/0.99  --sat_out_clauses                       false
% 3.21/0.99  
% 3.21/0.99  ------ QBF Options
% 3.21/0.99  
% 3.21/0.99  --qbf_mode                              false
% 3.21/0.99  --qbf_elim_univ                         false
% 3.21/0.99  --qbf_dom_inst                          none
% 3.21/0.99  --qbf_dom_pre_inst                      false
% 3.21/0.99  --qbf_sk_in                             false
% 3.21/0.99  --qbf_pred_elim                         true
% 3.21/0.99  --qbf_split                             512
% 3.21/0.99  
% 3.21/0.99  ------ BMC1 Options
% 3.21/0.99  
% 3.21/0.99  --bmc1_incremental                      false
% 3.21/0.99  --bmc1_axioms                           reachable_all
% 3.21/0.99  --bmc1_min_bound                        0
% 3.21/0.99  --bmc1_max_bound                        -1
% 3.21/0.99  --bmc1_max_bound_default                -1
% 3.21/0.99  --bmc1_symbol_reachability              true
% 3.21/0.99  --bmc1_property_lemmas                  false
% 3.21/0.99  --bmc1_k_induction                      false
% 3.21/0.99  --bmc1_non_equiv_states                 false
% 3.21/0.99  --bmc1_deadlock                         false
% 3.21/0.99  --bmc1_ucm                              false
% 3.21/0.99  --bmc1_add_unsat_core                   none
% 3.21/0.99  --bmc1_unsat_core_children              false
% 3.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/0.99  --bmc1_out_stat                         full
% 3.21/0.99  --bmc1_ground_init                      false
% 3.21/0.99  --bmc1_pre_inst_next_state              false
% 3.21/0.99  --bmc1_pre_inst_state                   false
% 3.21/0.99  --bmc1_pre_inst_reach_state             false
% 3.21/0.99  --bmc1_out_unsat_core                   false
% 3.21/0.99  --bmc1_aig_witness_out                  false
% 3.21/0.99  --bmc1_verbose                          false
% 3.21/0.99  --bmc1_dump_clauses_tptp                false
% 3.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.21/0.99  --bmc1_dump_file                        -
% 3.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.21/0.99  --bmc1_ucm_extend_mode                  1
% 3.21/0.99  --bmc1_ucm_init_mode                    2
% 3.21/0.99  --bmc1_ucm_cone_mode                    none
% 3.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.21/0.99  --bmc1_ucm_relax_model                  4
% 3.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/0.99  --bmc1_ucm_layered_model                none
% 3.21/0.99  --bmc1_ucm_max_lemma_size               10
% 3.21/0.99  
% 3.21/0.99  ------ AIG Options
% 3.21/0.99  
% 3.21/0.99  --aig_mode                              false
% 3.21/0.99  
% 3.21/0.99  ------ Instantiation Options
% 3.21/0.99  
% 3.21/0.99  --instantiation_flag                    true
% 3.21/0.99  --inst_sos_flag                         false
% 3.21/0.99  --inst_sos_phase                        true
% 3.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/0.99  --inst_lit_sel_side                     none
% 3.21/0.99  --inst_solver_per_active                1400
% 3.21/0.99  --inst_solver_calls_frac                1.
% 3.21/0.99  --inst_passive_queue_type               priority_queues
% 3.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/0.99  --inst_passive_queues_freq              [25;2]
% 3.21/0.99  --inst_dismatching                      true
% 3.21/0.99  --inst_eager_unprocessed_to_passive     true
% 3.21/0.99  --inst_prop_sim_given                   true
% 3.21/0.99  --inst_prop_sim_new                     false
% 3.21/0.99  --inst_subs_new                         false
% 3.21/0.99  --inst_eq_res_simp                      false
% 3.21/0.99  --inst_subs_given                       false
% 3.21/0.99  --inst_orphan_elimination               true
% 3.21/0.99  --inst_learning_loop_flag               true
% 3.21/0.99  --inst_learning_start                   3000
% 3.21/0.99  --inst_learning_factor                  2
% 3.21/0.99  --inst_start_prop_sim_after_learn       3
% 3.21/0.99  --inst_sel_renew                        solver
% 3.21/0.99  --inst_lit_activity_flag                true
% 3.21/0.99  --inst_restr_to_given                   false
% 3.21/0.99  --inst_activity_threshold               500
% 3.21/0.99  --inst_out_proof                        true
% 3.21/0.99  
% 3.21/0.99  ------ Resolution Options
% 3.21/0.99  
% 3.21/0.99  --resolution_flag                       false
% 3.21/0.99  --res_lit_sel                           adaptive
% 3.21/0.99  --res_lit_sel_side                      none
% 3.21/0.99  --res_ordering                          kbo
% 3.21/0.99  --res_to_prop_solver                    active
% 3.21/0.99  --res_prop_simpl_new                    false
% 3.21/0.99  --res_prop_simpl_given                  true
% 3.21/0.99  --res_passive_queue_type                priority_queues
% 3.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/0.99  --res_passive_queues_freq               [15;5]
% 3.21/0.99  --res_forward_subs                      full
% 3.21/0.99  --res_backward_subs                     full
% 3.21/0.99  --res_forward_subs_resolution           true
% 3.21/0.99  --res_backward_subs_resolution          true
% 3.21/0.99  --res_orphan_elimination                true
% 3.21/0.99  --res_time_limit                        2.
% 3.21/0.99  --res_out_proof                         true
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Options
% 3.21/0.99  
% 3.21/0.99  --superposition_flag                    true
% 3.21/0.99  --sup_passive_queue_type                priority_queues
% 3.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.21/0.99  --demod_completeness_check              fast
% 3.21/0.99  --demod_use_ground                      true
% 3.21/0.99  --sup_to_prop_solver                    passive
% 3.21/0.99  --sup_prop_simpl_new                    true
% 3.21/0.99  --sup_prop_simpl_given                  true
% 3.21/0.99  --sup_fun_splitting                     false
% 3.21/0.99  --sup_smt_interval                      50000
% 3.21/0.99  
% 3.21/0.99  ------ Superposition Simplification Setup
% 3.21/0.99  
% 3.21/0.99  --sup_indices_passive                   []
% 3.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_full_bw                           [BwDemod]
% 3.21/0.99  --sup_immed_triv                        [TrivRules]
% 3.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_immed_bw_main                     []
% 3.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/0.99  
% 3.21/0.99  ------ Combination Options
% 3.21/0.99  
% 3.21/0.99  --comb_res_mult                         3
% 3.21/0.99  --comb_sup_mult                         2
% 3.21/0.99  --comb_inst_mult                        10
% 3.21/0.99  
% 3.21/0.99  ------ Debug Options
% 3.21/0.99  
% 3.21/0.99  --dbg_backtrace                         false
% 3.21/0.99  --dbg_dump_prop_clauses                 false
% 3.21/0.99  --dbg_dump_prop_clauses_file            -
% 3.21/0.99  --dbg_out_stat                          false
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  ------ Proving...
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  % SZS status Theorem for theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  fof(f14,conjecture,(
% 3.21/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f15,negated_conjecture,(
% 3.21/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 3.21/0.99    inference(negated_conjecture,[],[f14])).
% 3.21/0.99  
% 3.21/0.99  fof(f34,plain,(
% 3.21/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : ((~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))) & m1_subset_1(X6,u1_struct_0(X2))) & (r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1))) & m1_subset_1(X5,u1_struct_0(X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f15])).
% 3.21/0.99  
% 3.21/0.99  fof(f35,plain,(
% 3.21/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.21/0.99    inference(flattening,[],[f34])).
% 3.21/0.99  
% 3.21/0.99  fof(f54,plain,(
% 3.21/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),sK8) & r2_hidden(sK8,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f53,plain,(
% 3.21/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),sK7))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,sK7) & v5_pre_topc(X3,X2,X1) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f52,plain,(
% 3.21/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,sK6),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,sK6,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK6,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK6))) )),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f51,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),sK5,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK5,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(sK5,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f50,plain,(
% 3.21/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,X0,k1_partfun1(u1_struct_0(sK4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK4),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(sK4))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,sK4,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f49,plain,(
% 3.21/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK3),X3,k6_domain_1(u1_struct_0(sK3),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(sK3,X0,X4,X5) & v5_pre_topc(X3,X2,sK3) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f48,plain,(
% 3.21/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK2,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK2),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,sK2,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f55,plain,(
% 3.21/0.99    ((((((~r1_tmap_1(sK4,sK2,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK6),sK8) & r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k6_domain_1(u1_struct_0(sK3),sK7))) & m1_subset_1(sK8,u1_struct_0(sK4))) & r1_tmap_1(sK3,sK2,sK6,sK7) & v5_pre_topc(sK5,sK4,sK3) & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f35,f54,f53,f52,f51,f50,f49,f48])).
% 3.21/0.99  
% 3.21/0.99  fof(f95,plain,(
% 3.21/0.99    m1_subset_1(sK7,u1_struct_0(sK3))),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f11,axiom,(
% 3.21/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f28,plain,(
% 3.21/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f11])).
% 3.21/0.99  
% 3.21/0.99  fof(f29,plain,(
% 3.21/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.21/0.99    inference(flattening,[],[f28])).
% 3.21/0.99  
% 3.21/0.99  fof(f75,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f29])).
% 3.21/0.99  
% 3.21/0.99  fof(f83,plain,(
% 3.21/0.99    ~v2_struct_0(sK3)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f85,plain,(
% 3.21/0.99    l1_pre_topc(sK3)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f10,axiom,(
% 3.21/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f26,plain,(
% 3.21/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f10])).
% 3.21/0.99  
% 3.21/0.99  fof(f27,plain,(
% 3.21/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.21/0.99    inference(flattening,[],[f26])).
% 3.21/0.99  
% 3.21/0.99  fof(f74,plain,(
% 3.21/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f27])).
% 3.21/0.99  
% 3.21/0.99  fof(f9,axiom,(
% 3.21/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f25,plain,(
% 3.21/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.21/0.99    inference(ennf_transformation,[],[f9])).
% 3.21/0.99  
% 3.21/0.99  fof(f73,plain,(
% 3.21/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f25])).
% 3.21/0.99  
% 3.21/0.99  fof(f99,plain,(
% 3.21/0.99    r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k6_domain_1(u1_struct_0(sK3),sK7)))),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f8,axiom,(
% 3.21/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)))))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f23,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : ((! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) | k1_xboole_0 = X1) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.21/0.99    inference(ennf_transformation,[],[f8])).
% 3.21/0.99  
% 3.21/0.99  fof(f24,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : (! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.21/0.99    inference(flattening,[],[f23])).
% 3.21/0.99  
% 3.21/0.99  fof(f42,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) | (~r2_hidden(k1_funct_1(X3,X4),X2) | ~r2_hidden(X4,X0))) & ((r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)) | ~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)))) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.21/0.99    inference(nnf_transformation,[],[f24])).
% 3.21/0.99  
% 3.21/0.99  fof(f43,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : (! [X4] : ((r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) | ~r2_hidden(k1_funct_1(X3,X4),X2) | ~r2_hidden(X4,X0)) & ((r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)) | ~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)))) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.21/0.99    inference(flattening,[],[f42])).
% 3.21/0.99  
% 3.21/0.99  fof(f71,plain,(
% 3.21/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X4),X2) | ~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f43])).
% 3.21/0.99  
% 3.21/0.99  fof(f89,plain,(
% 3.21/0.99    v1_funct_1(sK5)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f90,plain,(
% 3.21/0.99    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f91,plain,(
% 3.21/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f2,axiom,(
% 3.21/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f36,plain,(
% 3.21/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.21/0.99    inference(nnf_transformation,[],[f2])).
% 3.21/0.99  
% 3.21/0.99  fof(f37,plain,(
% 3.21/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.21/0.99    inference(rectify,[],[f36])).
% 3.21/0.99  
% 3.21/0.99  fof(f38,plain,(
% 3.21/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f39,plain,(
% 3.21/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.21/0.99  
% 3.21/0.99  fof(f57,plain,(
% 3.21/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.21/0.99    inference(cnf_transformation,[],[f39])).
% 3.21/0.99  
% 3.21/0.99  fof(f103,plain,(
% 3.21/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.21/0.99    inference(equality_resolution,[],[f57])).
% 3.21/0.99  
% 3.21/0.99  fof(f13,axiom,(
% 3.21/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f32,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f13])).
% 3.21/0.99  
% 3.21/0.99  fof(f33,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.99    inference(flattening,[],[f32])).
% 3.21/0.99  
% 3.21/0.99  fof(f79,plain,(
% 3.21/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f33])).
% 3.21/0.99  
% 3.21/0.99  fof(f106,plain,(
% 3.21/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.21/0.99    inference(equality_resolution,[],[f79])).
% 3.21/0.99  
% 3.21/0.99  fof(f100,plain,(
% 3.21/0.99    ~r1_tmap_1(sK4,sK2,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK6),sK8)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f98,plain,(
% 3.21/0.99    m1_subset_1(sK8,u1_struct_0(sK4))),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f7,axiom,(
% 3.21/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f21,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f7])).
% 3.21/0.99  
% 3.21/0.99  fof(f22,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.21/0.99    inference(flattening,[],[f21])).
% 3.21/0.99  
% 3.21/0.99  fof(f69,plain,(
% 3.21/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f22])).
% 3.21/0.99  
% 3.21/0.99  fof(f86,plain,(
% 3.21/0.99    ~v2_struct_0(sK4)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f88,plain,(
% 3.21/0.99    l1_pre_topc(sK4)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f80,plain,(
% 3.21/0.99    ~v2_struct_0(sK2)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f81,plain,(
% 3.21/0.99    v2_pre_topc(sK2)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f82,plain,(
% 3.21/0.99    l1_pre_topc(sK2)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f84,plain,(
% 3.21/0.99    v2_pre_topc(sK3)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f87,plain,(
% 3.21/0.99    v2_pre_topc(sK4)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f92,plain,(
% 3.21/0.99    v1_funct_1(sK6)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f93,plain,(
% 3.21/0.99    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f94,plain,(
% 3.21/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f12,axiom,(
% 3.21/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f30,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f12])).
% 3.21/0.99  
% 3.21/0.99  fof(f31,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.99    inference(flattening,[],[f30])).
% 3.21/0.99  
% 3.21/0.99  fof(f44,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.99    inference(nnf_transformation,[],[f31])).
% 3.21/0.99  
% 3.21/0.99  fof(f45,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.99    inference(rectify,[],[f44])).
% 3.21/0.99  
% 3.21/0.99  fof(f46,plain,(
% 3.21/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1))))),
% 3.21/0.99    introduced(choice_axiom,[])).
% 3.21/0.99  
% 3.21/0.99  fof(f47,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 3.21/0.99  
% 3.21/0.99  fof(f76,plain,(
% 3.21/0.99    ( ! [X4,X2,X0,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~v5_pre_topc(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f47])).
% 3.21/0.99  
% 3.21/0.99  fof(f96,plain,(
% 3.21/0.99    v5_pre_topc(sK5,sK4,sK3)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f6,axiom,(
% 3.21/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f19,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f6])).
% 3.21/0.99  
% 3.21/0.99  fof(f20,plain,(
% 3.21/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.21/0.99    inference(flattening,[],[f19])).
% 3.21/0.99  
% 3.21/0.99  fof(f68,plain,(
% 3.21/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f20])).
% 3.21/0.99  
% 3.21/0.99  fof(f97,plain,(
% 3.21/0.99    r1_tmap_1(sK3,sK2,sK6,sK7)),
% 3.21/0.99    inference(cnf_transformation,[],[f55])).
% 3.21/0.99  
% 3.21/0.99  fof(f4,axiom,(
% 3.21/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f16,plain,(
% 3.21/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.21/0.99    inference(ennf_transformation,[],[f4])).
% 3.21/0.99  
% 3.21/0.99  fof(f64,plain,(
% 3.21/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f16])).
% 3.21/0.99  
% 3.21/0.99  fof(f3,axiom,(
% 3.21/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f40,plain,(
% 3.21/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.21/0.99    inference(nnf_transformation,[],[f3])).
% 3.21/0.99  
% 3.21/0.99  fof(f41,plain,(
% 3.21/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.21/0.99    inference(flattening,[],[f40])).
% 3.21/0.99  
% 3.21/0.99  fof(f62,plain,(
% 3.21/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.21/0.99    inference(cnf_transformation,[],[f41])).
% 3.21/0.99  
% 3.21/0.99  fof(f105,plain,(
% 3.21/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.21/0.99    inference(equality_resolution,[],[f62])).
% 3.21/0.99  
% 3.21/0.99  fof(f5,axiom,(
% 3.21/0.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f17,plain,(
% 3.21/0.99    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.21/0.99    inference(ennf_transformation,[],[f5])).
% 3.21/0.99  
% 3.21/0.99  fof(f18,plain,(
% 3.21/0.99    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.21/0.99    inference(flattening,[],[f17])).
% 3.21/0.99  
% 3.21/0.99  fof(f66,plain,(
% 3.21/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.21/0.99    inference(cnf_transformation,[],[f18])).
% 3.21/0.99  
% 3.21/0.99  fof(f1,axiom,(
% 3.21/0.99    v1_xboole_0(k1_xboole_0)),
% 3.21/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.21/0.99  
% 3.21/0.99  fof(f56,plain,(
% 3.21/0.99    v1_xboole_0(k1_xboole_0)),
% 3.21/0.99    inference(cnf_transformation,[],[f1])).
% 3.21/0.99  
% 3.21/0.99  cnf(c_29,negated_conjecture,
% 3.21/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1510,plain,
% 3.21/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_19,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,X1)
% 3.21/0.99      | v1_xboole_0(X1)
% 3.21/0.99      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1516,plain,
% 3.21/0.99      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.21/0.99      | m1_subset_1(X1,X0) != iProver_top
% 3.21/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3389,plain,
% 3.21/0.99      ( k6_domain_1(u1_struct_0(sK3),sK7) = k1_tarski(sK7)
% 3.21/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1510,c_1516]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_41,negated_conjecture,
% 3.21/0.99      ( ~ v2_struct_0(sK3) ),
% 3.21/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_39,negated_conjecture,
% 3.21/0.99      ( l1_pre_topc(sK3) ),
% 3.21/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_18,plain,
% 3.21/0.99      ( v2_struct_0(X0)
% 3.21/0.99      | ~ l1_struct_0(X0)
% 3.21/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_82,plain,
% 3.21/0.99      ( v2_struct_0(sK3)
% 3.21/0.99      | ~ l1_struct_0(sK3)
% 3.21/0.99      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_17,plain,
% 3.21/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_85,plain,
% 3.21/0.99      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1910,plain,
% 3.21/0.99      ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 3.21/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.21/0.99      | k6_domain_1(u1_struct_0(sK3),sK7) = k1_tarski(sK7) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3645,plain,
% 3.21/0.99      ( k6_domain_1(u1_struct_0(sK3),sK7) = k1_tarski(sK7) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_3389,c_41,c_39,c_29,c_82,c_85,c_1910]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_25,negated_conjecture,
% 3.21/0.99      ( r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k6_domain_1(u1_struct_0(sK3),sK7))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1513,plain,
% 3.21/0.99      ( r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k6_domain_1(u1_struct_0(sK3),sK7))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3648,plain,
% 3.21/0.99      ( r2_hidden(sK8,k8_relset_1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k1_tarski(sK7))) = iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_3645,c_1513]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_15,plain,
% 3.21/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | ~ r2_hidden(X3,k8_relset_1(X1,X2,X0,X4))
% 3.21/0.99      | r2_hidden(k1_funct_1(X0,X3),X4)
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | k1_xboole_0 = X2 ),
% 3.21/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1518,plain,
% 3.21/0.99      ( k1_xboole_0 = X0
% 3.21/0.99      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.21/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.21/0.99      | r2_hidden(X3,k8_relset_1(X2,X0,X1,X4)) != iProver_top
% 3.21/0.99      | r2_hidden(k1_funct_1(X1,X3),X4) = iProver_top
% 3.21/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4371,plain,
% 3.21/0.99      ( u1_struct_0(sK3) = k1_xboole_0
% 3.21/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.21/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.21/0.99      | r2_hidden(k1_funct_1(sK5,sK8),k1_tarski(sK7)) = iProver_top
% 3.21/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3648,c_1518]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_35,negated_conjecture,
% 3.21/0.99      ( v1_funct_1(sK5) ),
% 3.21/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_54,plain,
% 3.21/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_34,negated_conjecture,
% 3.21/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_55,plain,
% 3.21/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_33,negated_conjecture,
% 3.21/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_56,plain,
% 3.21/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5070,plain,
% 3.21/0.99      ( r2_hidden(k1_funct_1(sK5,sK8),k1_tarski(sK7)) = iProver_top
% 3.21/0.99      | u1_struct_0(sK3) = k1_xboole_0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_4371,c_54,c_55,c_56]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5071,plain,
% 3.21/0.99      ( u1_struct_0(sK3) = k1_xboole_0
% 3.21/0.99      | r2_hidden(k1_funct_1(sK5,sK8),k1_tarski(sK7)) = iProver_top ),
% 3.21/0.99      inference(renaming,[status(thm)],[c_5070]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4,plain,
% 3.21/0.99      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.21/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1524,plain,
% 3.21/0.99      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_5076,plain,
% 3.21/0.99      ( k1_funct_1(sK5,sK8) = sK7 | u1_struct_0(sK3) = k1_xboole_0 ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_5071,c_1524]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_23,plain,
% 3.21/0.99      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.21/0.99      | ~ r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
% 3.21/0.99      | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3)
% 3.21/0.99      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
% 3.21/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.21/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.21/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.21/0.99      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1))
% 3.21/0.99      | ~ v2_pre_topc(X0)
% 3.21/0.99      | ~ v2_pre_topc(X4)
% 3.21/0.99      | ~ v2_pre_topc(X1)
% 3.21/0.99      | v2_struct_0(X4)
% 3.21/0.99      | v2_struct_0(X0)
% 3.21/0.99      | v2_struct_0(X1)
% 3.21/0.99      | ~ l1_pre_topc(X4)
% 3.21/0.99      | ~ l1_pre_topc(X0)
% 3.21/0.99      | ~ l1_pre_topc(X1)
% 3.21/0.99      | ~ v1_funct_1(X2)
% 3.21/0.99      | ~ v1_funct_1(X5) ),
% 3.21/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1515,plain,
% 3.21/0.99      ( r1_tmap_1(X0,X1,X2,X3) != iProver_top
% 3.21/0.99      | r1_tmap_1(X1,X4,X5,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) != iProver_top
% 3.21/0.99      | r1_tmap_1(X0,X4,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X4),X2,X5),X3) = iProver_top
% 3.21/0.99      | v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4)) != iProver_top
% 3.21/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.21/0.99      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.21/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) != iProver_top
% 3.21/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.21/0.99      | m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(X1)) != iProver_top
% 3.21/0.99      | v2_pre_topc(X0) != iProver_top
% 3.21/0.99      | v2_pre_topc(X4) != iProver_top
% 3.21/0.99      | v2_pre_topc(X1) != iProver_top
% 3.21/0.99      | v2_struct_0(X4) = iProver_top
% 3.21/0.99      | v2_struct_0(X0) = iProver_top
% 3.21/0.99      | v2_struct_0(X1) = iProver_top
% 3.21/0.99      | l1_pre_topc(X4) != iProver_top
% 3.21/0.99      | l1_pre_topc(X0) != iProver_top
% 3.21/0.99      | l1_pre_topc(X1) != iProver_top
% 3.21/0.99      | v1_funct_1(X2) != iProver_top
% 3.21/0.99      | v1_funct_1(X5) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_24,negated_conjecture,
% 3.21/0.99      ( ~ r1_tmap_1(sK4,sK2,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK6),sK8) ),
% 3.21/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1514,plain,
% 3.21/0.99      ( r1_tmap_1(sK4,sK2,k1_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK6),sK8) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4975,plain,
% 3.21/0.99      ( r1_tmap_1(sK3,sK2,sK6,k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK8)) != iProver_top
% 3.21/0.99      | r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
% 3.21/0.99      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.21/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.21/0.99      | m1_subset_1(k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK8),u1_struct_0(sK3)) != iProver_top
% 3.21/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.21/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.21/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.21/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.21/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.21/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.21/0.99      | v2_struct_0(sK3) = iProver_top
% 3.21/0.99      | v2_struct_0(sK2) = iProver_top
% 3.21/0.99      | v2_struct_0(sK4) = iProver_top
% 3.21/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.21/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.21/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.21/0.99      | v1_funct_1(sK6) != iProver_top
% 3.21/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1515,c_1514]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_26,negated_conjecture,
% 3.21/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1512,plain,
% 3.21/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1506,plain,
% 3.21/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_13,plain,
% 3.21/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.21/0.99      | ~ m1_subset_1(X3,X1)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | v1_xboole_0(X1)
% 3.21/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.21/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1520,plain,
% 3.21/0.99      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 3.21/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.21/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.21/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.21/0.99      | v1_funct_1(X2) != iProver_top
% 3.21/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4033,plain,
% 3.21/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
% 3.21/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.21/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
% 3.21/0.99      | v1_funct_1(sK5) != iProver_top
% 3.21/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1506,c_1520]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_38,negated_conjecture,
% 3.21/0.99      ( ~ v2_struct_0(sK4) ),
% 3.21/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_51,plain,
% 3.21/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_36,negated_conjecture,
% 3.21/0.99      ( l1_pre_topc(sK4) ),
% 3.21/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_53,plain,
% 3.21/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_428,plain,
% 3.21/0.99      ( v2_struct_0(X0)
% 3.21/0.99      | ~ l1_pre_topc(X0)
% 3.21/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.21/0.99      inference(resolution,[status(thm)],[c_17,c_18]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2090,plain,
% 3.21/0.99      ( v2_struct_0(sK4)
% 3.21/0.99      | ~ l1_pre_topc(sK4)
% 3.21/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_428]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_2091,plain,
% 3.21/0.99      ( v2_struct_0(sK4) = iProver_top
% 3.21/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.21/0.99      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_2090]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4852,plain,
% 3.21/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) = k1_funct_1(sK5,X0)
% 3.21/0.99      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_4033,c_51,c_53,c_54,c_55,c_2091]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4861,plain,
% 3.21/0.99      ( k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK8) = k1_funct_1(sK5,sK8) ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1512,c_4852]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4976,plain,
% 3.21/0.99      ( r1_tmap_1(sK3,sK2,sK6,k1_funct_1(sK5,sK8)) != iProver_top
% 3.21/0.99      | r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
% 3.21/0.99      | v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.21/0.99      | v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.21/0.99      | m1_subset_1(k1_funct_1(sK5,sK8),u1_struct_0(sK3)) != iProver_top
% 3.21/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.21/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
% 3.21/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.21/0.99      | v2_pre_topc(sK3) != iProver_top
% 3.21/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.21/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.21/0.99      | v2_struct_0(sK3) = iProver_top
% 3.21/0.99      | v2_struct_0(sK2) = iProver_top
% 3.21/0.99      | v2_struct_0(sK4) = iProver_top
% 3.21/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.21/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.21/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.21/0.99      | v1_funct_1(sK6) != iProver_top
% 3.21/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.21/0.99      inference(light_normalisation,[status(thm)],[c_4975,c_4861]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_44,negated_conjecture,
% 3.21/0.99      ( ~ v2_struct_0(sK2) ),
% 3.21/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_45,plain,
% 3.21/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_43,negated_conjecture,
% 3.21/0.99      ( v2_pre_topc(sK2) ),
% 3.21/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_46,plain,
% 3.21/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_42,negated_conjecture,
% 3.21/0.99      ( l1_pre_topc(sK2) ),
% 3.21/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_47,plain,
% 3.21/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_48,plain,
% 3.21/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_40,negated_conjecture,
% 3.21/0.99      ( v2_pre_topc(sK3) ),
% 3.21/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_49,plain,
% 3.21/0.99      ( v2_pre_topc(sK3) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_50,plain,
% 3.21/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_37,negated_conjecture,
% 3.21/0.99      ( v2_pre_topc(sK4) ),
% 3.21/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_52,plain,
% 3.21/0.99      ( v2_pre_topc(sK4) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_32,negated_conjecture,
% 3.21/0.99      ( v1_funct_1(sK6) ),
% 3.21/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_57,plain,
% 3.21/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_31,negated_conjecture,
% 3.21/0.99      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.21/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_58,plain,
% 3.21/0.99      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_30,negated_conjecture,
% 3.21/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 3.21/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_59,plain,
% 3.21/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_63,plain,
% 3.21/0.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_22,plain,
% 3.21/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.21/0.99      | ~ v5_pre_topc(X2,X0,X1)
% 3.21/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.21/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.21/0.99      | ~ v2_pre_topc(X0)
% 3.21/0.99      | ~ v2_pre_topc(X1)
% 3.21/0.99      | v2_struct_0(X1)
% 3.21/0.99      | v2_struct_0(X0)
% 3.21/0.99      | ~ l1_pre_topc(X1)
% 3.21/0.99      | ~ l1_pre_topc(X0)
% 3.21/0.99      | ~ v1_funct_1(X2) ),
% 3.21/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_28,negated_conjecture,
% 3.21/0.99      ( v5_pre_topc(sK5,sK4,sK3) ),
% 3.21/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_529,plain,
% 3.21/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.21/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.21/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.21/0.99      | ~ v2_pre_topc(X1)
% 3.21/0.99      | ~ v2_pre_topc(X0)
% 3.21/0.99      | v2_struct_0(X0)
% 3.21/0.99      | v2_struct_0(X1)
% 3.21/0.99      | ~ l1_pre_topc(X0)
% 3.21/0.99      | ~ l1_pre_topc(X1)
% 3.21/0.99      | ~ v1_funct_1(X2)
% 3.21/0.99      | sK5 != X2
% 3.21/0.99      | sK3 != X1
% 3.21/0.99      | sK4 != X0 ),
% 3.21/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_530,plain,
% 3.21/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0)
% 3.21/0.99      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
% 3.21/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.21/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.21/0.99      | ~ v2_pre_topc(sK3)
% 3.21/0.99      | ~ v2_pre_topc(sK4)
% 3.21/0.99      | v2_struct_0(sK3)
% 3.21/0.99      | v2_struct_0(sK4)
% 3.21/0.99      | ~ l1_pre_topc(sK3)
% 3.21/0.99      | ~ l1_pre_topc(sK4)
% 3.21/0.99      | ~ v1_funct_1(sK5) ),
% 3.21/0.99      inference(unflattening,[status(thm)],[c_529]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_534,plain,
% 3.21/0.99      ( r1_tmap_1(sK4,sK3,sK5,X0) | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_530,c_41,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1876,plain,
% 3.21/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8)
% 3.21/0.99      | ~ m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_534]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1877,plain,
% 3.21/0.99      ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
% 3.21/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_1876]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_12,plain,
% 3.21/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.21/0.99      | ~ m1_subset_1(X3,X1)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | v1_xboole_0(X1) ),
% 3.21/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1521,plain,
% 3.21/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.21/0.99      | m1_subset_1(X3,X1) != iProver_top
% 3.21/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.21/0.99      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 3.21/0.99      | v1_funct_1(X0) != iProver_top
% 3.21/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_4880,plain,
% 3.21/0.99      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 3.21/0.99      | m1_subset_1(k1_funct_1(sK5,sK8),u1_struct_0(sK3)) = iProver_top
% 3.21/0.99      | m1_subset_1(sK8,u1_struct_0(sK4)) != iProver_top
% 3.21/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 3.21/0.99      | v1_funct_1(sK5) != iProver_top
% 3.21/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_4861,c_1521]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6472,plain,
% 3.21/0.99      ( r1_tmap_1(sK3,sK2,sK6,k1_funct_1(sK5,sK8)) != iProver_top ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_4976,c_45,c_46,c_47,c_48,c_49,c_50,c_51,c_52,c_53,
% 3.21/0.99                 c_54,c_55,c_56,c_57,c_58,c_59,c_63,c_1877,c_2091,c_4880]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6480,plain,
% 3.21/0.99      ( u1_struct_0(sK3) = k1_xboole_0
% 3.21/0.99      | r1_tmap_1(sK3,sK2,sK6,sK7) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_5076,c_6472]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_27,negated_conjecture,
% 3.21/0.99      ( r1_tmap_1(sK3,sK2,sK6,sK7) ),
% 3.21/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_62,plain,
% 3.21/0.99      ( r1_tmap_1(sK3,sK2,sK6,sK7) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6539,plain,
% 3.21/0.99      ( u1_struct_0(sK3) = k1_xboole_0 ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_6480,c_62]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1509,plain,
% 3.21/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_8,plain,
% 3.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.21/0.99      | ~ v1_xboole_0(X1)
% 3.21/0.99      | v1_xboole_0(X0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1523,plain,
% 3.21/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.21/0.99      | v1_xboole_0(X1) != iProver_top
% 3.21/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3154,plain,
% 3.21/0.99      ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) != iProver_top
% 3.21/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1509,c_1523]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6563,plain,
% 3.21/0.99      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) != iProver_top
% 3.21/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_6539,c_3154]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6,plain,
% 3.21/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.21/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_6586,plain,
% 3.21/0.99      ( v1_xboole_0(sK6) = iProver_top
% 3.21/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.21/0.99      inference(demodulation,[status(thm)],[c_6563,c_6]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_10,plain,
% 3.21/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.21/0.99      | ~ v1_funct_1(X0)
% 3.21/0.99      | ~ v1_xboole_0(X0)
% 3.21/0.99      | v1_xboole_0(X1)
% 3.21/0.99      | v1_xboole_0(X2) ),
% 3.21/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1522,plain,
% 3.21/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.21/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.21/0.99      | v1_funct_1(X0) != iProver_top
% 3.21/0.99      | v1_xboole_0(X0) != iProver_top
% 3.21/0.99      | v1_xboole_0(X1) = iProver_top
% 3.21/0.99      | v1_xboole_0(X2) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3510,plain,
% 3.21/0.99      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.21/0.99      | v1_funct_1(sK6) != iProver_top
% 3.21/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 3.21/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.21/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_1509,c_1522]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_81,plain,
% 3.21/0.99      ( v2_struct_0(X0) = iProver_top
% 3.21/0.99      | l1_struct_0(X0) != iProver_top
% 3.21/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_83,plain,
% 3.21/0.99      ( v2_struct_0(sK3) = iProver_top
% 3.21/0.99      | l1_struct_0(sK3) != iProver_top
% 3.21/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_81]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_84,plain,
% 3.21/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_86,plain,
% 3.21/0.99      ( l1_pre_topc(sK3) != iProver_top
% 3.21/0.99      | l1_struct_0(sK3) = iProver_top ),
% 3.21/0.99      inference(instantiation,[status(thm)],[c_84]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3734,plain,
% 3.21/0.99      ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.21/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 3.21/0.99      inference(global_propositional_subsumption,
% 3.21/0.99                [status(thm)],
% 3.21/0.99                [c_3510,c_48,c_50,c_57,c_58,c_83,c_86]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_1494,plain,
% 3.21/0.99      ( v2_struct_0(X0) = iProver_top
% 3.21/0.99      | l1_pre_topc(X0) != iProver_top
% 3.21/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_3740,plain,
% 3.21/0.99      ( v2_struct_0(sK2) = iProver_top
% 3.21/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.21/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 3.21/0.99      inference(superposition,[status(thm)],[c_3734,c_1494]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_0,plain,
% 3.21/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.21/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(c_121,plain,
% 3.21/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.21/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/0.99  
% 3.21/0.99  cnf(contradiction,plain,
% 3.21/0.99      ( $false ),
% 3.21/0.99      inference(minisat,[status(thm)],[c_6586,c_3740,c_121,c_47,c_45]) ).
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/0.99  
% 3.21/0.99  ------                               Statistics
% 3.21/0.99  
% 3.21/0.99  ------ General
% 3.21/0.99  
% 3.21/0.99  abstr_ref_over_cycles:                  0
% 3.21/0.99  abstr_ref_under_cycles:                 0
% 3.21/0.99  gc_basic_clause_elim:                   0
% 3.21/0.99  forced_gc_time:                         0
% 3.21/0.99  parsing_time:                           0.013
% 3.21/0.99  unif_index_cands_time:                  0.
% 3.21/0.99  unif_index_add_time:                    0.
% 3.21/0.99  orderings_time:                         0.
% 3.21/0.99  out_proof_time:                         0.015
% 3.21/0.99  total_time:                             0.284
% 3.21/0.99  num_of_symbols:                         61
% 3.21/0.99  num_of_terms:                           10173
% 3.21/0.99  
% 3.21/0.99  ------ Preprocessing
% 3.21/0.99  
% 3.21/0.99  num_of_splits:                          0
% 3.21/0.99  num_of_split_atoms:                     0
% 3.21/0.99  num_of_reused_defs:                     0
% 3.21/0.99  num_eq_ax_congr_red:                    31
% 3.21/0.99  num_of_sem_filtered_clauses:            1
% 3.21/0.99  num_of_subtypes:                        0
% 3.21/0.99  monotx_restored_types:                  0
% 3.21/0.99  sat_num_of_epr_types:                   0
% 3.21/0.99  sat_num_of_non_cyclic_types:            0
% 3.21/0.99  sat_guarded_non_collapsed_types:        0
% 3.21/0.99  num_pure_diseq_elim:                    0
% 3.21/0.99  simp_replaced_by:                       0
% 3.21/0.99  res_preprocessed:                       203
% 3.21/0.99  prep_upred:                             0
% 3.21/0.99  prep_unflattend:                        6
% 3.21/0.99  smt_new_axioms:                         0
% 3.21/0.99  pred_elim_cands:                        9
% 3.21/0.99  pred_elim:                              2
% 3.21/0.99  pred_elim_cl:                           2
% 3.21/0.99  pred_elim_cycles:                       4
% 3.21/0.99  merged_defs:                            0
% 3.21/0.99  merged_defs_ncl:                        0
% 3.21/0.99  bin_hyper_res:                          0
% 3.21/0.99  prep_cycles:                            4
% 3.21/0.99  pred_elim_time:                         0.006
% 3.21/0.99  splitting_time:                         0.
% 3.21/0.99  sem_filter_time:                        0.
% 3.21/0.99  monotx_time:                            0.001
% 3.21/0.99  subtype_inf_time:                       0.
% 3.21/0.99  
% 3.21/0.99  ------ Problem properties
% 3.21/0.99  
% 3.21/0.99  clauses:                                41
% 3.21/0.99  conjectures:                            20
% 3.21/0.99  epr:                                    13
% 3.21/0.99  horn:                                   29
% 3.21/0.99  ground:                                 21
% 3.21/0.99  unary:                                  24
% 3.21/0.99  binary:                                 2
% 3.21/0.99  lits:                                   127
% 3.21/0.99  lits_eq:                                15
% 3.21/0.99  fd_pure:                                0
% 3.21/0.99  fd_pseudo:                              0
% 3.21/0.99  fd_cond:                                4
% 3.21/0.99  fd_pseudo_cond:                         2
% 3.21/0.99  ac_symbols:                             0
% 3.21/0.99  
% 3.21/0.99  ------ Propositional Solver
% 3.21/0.99  
% 3.21/0.99  prop_solver_calls:                      27
% 3.21/0.99  prop_fast_solver_calls:                 1668
% 3.21/0.99  smt_solver_calls:                       0
% 3.21/0.99  smt_fast_solver_calls:                  0
% 3.21/0.99  prop_num_of_clauses:                    2573
% 3.21/0.99  prop_preprocess_simplified:             7591
% 3.21/0.99  prop_fo_subsumed:                       84
% 3.21/0.99  prop_solver_time:                       0.
% 3.21/0.99  smt_solver_time:                        0.
% 3.21/0.99  smt_fast_solver_time:                   0.
% 3.21/0.99  prop_fast_solver_time:                  0.
% 3.21/0.99  prop_unsat_core_time:                   0.
% 3.21/0.99  
% 3.21/0.99  ------ QBF
% 3.21/0.99  
% 3.21/0.99  qbf_q_res:                              0
% 3.21/0.99  qbf_num_tautologies:                    0
% 3.21/0.99  qbf_prep_cycles:                        0
% 3.21/0.99  
% 3.21/0.99  ------ BMC1
% 3.21/0.99  
% 3.21/0.99  bmc1_current_bound:                     -1
% 3.21/0.99  bmc1_last_solved_bound:                 -1
% 3.21/0.99  bmc1_unsat_core_size:                   -1
% 3.21/0.99  bmc1_unsat_core_parents_size:           -1
% 3.21/0.99  bmc1_merge_next_fun:                    0
% 3.21/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.21/0.99  
% 3.21/0.99  ------ Instantiation
% 3.21/0.99  
% 3.21/0.99  inst_num_of_clauses:                    678
% 3.21/0.99  inst_num_in_passive:                    110
% 3.21/0.99  inst_num_in_active:                     384
% 3.21/0.99  inst_num_in_unprocessed:                184
% 3.21/0.99  inst_num_of_loops:                      410
% 3.21/0.99  inst_num_of_learning_restarts:          0
% 3.21/0.99  inst_num_moves_active_passive:          24
% 3.21/0.99  inst_lit_activity:                      0
% 3.21/0.99  inst_lit_activity_moves:                0
% 3.21/0.99  inst_num_tautologies:                   0
% 3.21/0.99  inst_num_prop_implied:                  0
% 3.21/0.99  inst_num_existing_simplified:           0
% 3.21/0.99  inst_num_eq_res_simplified:             0
% 3.21/0.99  inst_num_child_elim:                    0
% 3.21/0.99  inst_num_of_dismatching_blockings:      61
% 3.21/0.99  inst_num_of_non_proper_insts:           478
% 3.21/0.99  inst_num_of_duplicates:                 0
% 3.21/0.99  inst_inst_num_from_inst_to_res:         0
% 3.21/0.99  inst_dismatching_checking_time:         0.
% 3.21/0.99  
% 3.21/0.99  ------ Resolution
% 3.21/0.99  
% 3.21/0.99  res_num_of_clauses:                     0
% 3.21/0.99  res_num_in_passive:                     0
% 3.21/0.99  res_num_in_active:                      0
% 3.21/0.99  res_num_of_loops:                       207
% 3.21/0.99  res_forward_subset_subsumed:            41
% 3.21/0.99  res_backward_subset_subsumed:           0
% 3.21/0.99  res_forward_subsumed:                   0
% 3.21/0.99  res_backward_subsumed:                  0
% 3.21/0.99  res_forward_subsumption_resolution:     0
% 3.21/0.99  res_backward_subsumption_resolution:    0
% 3.21/0.99  res_clause_to_clause_subsumption:       364
% 3.21/0.99  res_orphan_elimination:                 0
% 3.21/0.99  res_tautology_del:                      18
% 3.21/0.99  res_num_eq_res_simplified:              0
% 3.21/0.99  res_num_sel_changes:                    0
% 3.21/0.99  res_moves_from_active_to_pass:          0
% 3.21/0.99  
% 3.21/0.99  ------ Superposition
% 3.21/0.99  
% 3.21/0.99  sup_time_total:                         0.
% 3.21/0.99  sup_time_generating:                    0.
% 3.21/0.99  sup_time_sim_full:                      0.
% 3.21/0.99  sup_time_sim_immed:                     0.
% 3.21/0.99  
% 3.21/0.99  sup_num_of_clauses:                     97
% 3.21/0.99  sup_num_in_active:                      48
% 3.21/0.99  sup_num_in_passive:                     49
% 3.21/0.99  sup_num_of_loops:                       81
% 3.21/0.99  sup_fw_superposition:                   48
% 3.21/0.99  sup_bw_superposition:                   42
% 3.21/0.99  sup_immediate_simplified:               31
% 3.21/0.99  sup_given_eliminated:                   0
% 3.21/0.99  comparisons_done:                       0
% 3.21/0.99  comparisons_avoided:                    15
% 3.21/0.99  
% 3.21/0.99  ------ Simplifications
% 3.21/0.99  
% 3.21/0.99  
% 3.21/0.99  sim_fw_subset_subsumed:                 11
% 3.21/0.99  sim_bw_subset_subsumed:                 5
% 3.21/0.99  sim_fw_subsumed:                        8
% 3.21/0.99  sim_bw_subsumed:                        1
% 3.21/0.99  sim_fw_subsumption_res:                 2
% 3.21/0.99  sim_bw_subsumption_res:                 0
% 3.21/0.99  sim_tautology_del:                      2
% 3.21/0.99  sim_eq_tautology_del:                   3
% 3.21/0.99  sim_eq_res_simp:                        0
% 3.21/0.99  sim_fw_demodulated:                     6
% 3.21/0.99  sim_bw_demodulated:                     29
% 3.21/0.99  sim_light_normalised:                   5
% 3.21/0.99  sim_joinable_taut:                      0
% 3.21/0.99  sim_joinable_simp:                      0
% 3.21/0.99  sim_ac_normalised:                      0
% 3.21/0.99  sim_smt_subsumption:                    0
% 3.21/0.99  
%------------------------------------------------------------------------------
