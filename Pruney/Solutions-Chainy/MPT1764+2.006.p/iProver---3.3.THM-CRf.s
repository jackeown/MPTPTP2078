%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:56 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 741 expanded)
%              Number of clauses        :   74 ( 161 expanded)
%              Number of leaves         :   13 ( 326 expanded)
%              Depth                    :   23
%              Number of atoms          :  575 (9990 expanded)
%              Number of equality atoms :  166 (1037 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
                           => ( r1_tarski(X5,u1_struct_0(X2))
                             => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                             => ( r1_tarski(X5,u1_struct_0(X2))
                               => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & r1_tarski(X5,u1_struct_0(X2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & r1_tarski(sK5,u1_struct_0(X2))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
              & r1_tarski(X5,u1_struct_0(X2))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5)
            & r1_tarski(X5,u1_struct_0(X2))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                  & r1_tarski(X5,u1_struct_0(X2))
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5)
                & r1_tarski(X5,u1_struct_0(X2))
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                      & r1_tarski(X5,u1_struct_0(X2))
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                  & m1_pre_topc(X2,X3)
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
                    ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5)
                    & r1_tarski(X5,u1_struct_0(sK2))
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
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
                        ( k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5)
                        & r1_tarski(X5,u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & r1_tarski(X5,u1_struct_0(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                        & m1_pre_topc(X2,X3)
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
                          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & r1_tarski(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & r1_tarski(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f25,f24,f23,f22,f21,f20])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_442,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_855,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_444,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_853,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_447,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_850,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_454,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | v2_struct_0(X3_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_51,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_844,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_51,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_1932,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_844])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_29,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_36,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2114,plain,
    ( v2_pre_topc(X1_55) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1932,c_28,c_29,c_30,c_35,c_36])).

cnf(c_2115,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2114])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(X0_53,X1_53,X0_51,X2_53) = k7_relat_1(X0_51,X2_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_843,plain,
    ( k2_partfun1(X0_53,X1_53,X0_51,X2_53) = k7_relat_1(X0_51,X2_53)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_1606,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_843])).

cnf(c_1083,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_2043,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1606,c_14,c_12,c_1083])).

cnf(c_2120,plain,
    ( k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2115,c_2043])).

cnf(c_2131,plain,
    ( k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK0) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_2120])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_25,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_26,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2136,plain,
    ( m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(X0_55,sK0) != iProver_top
    | k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2131,c_25,c_26,c_27])).

cnf(c_2137,plain,
    ( k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK0) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2136])).

cnf(c_2146,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_855,c_2137])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_38,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2318,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2146,c_38])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | v2_struct_0(X3_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_845,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_2322,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2318,c_845])).

cnf(c_32,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_34,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2822,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2322,c_25,c_26,c_27,c_28,c_29,c_30,c_32,c_34,c_35,c_36,c_37])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k7_relset_1(X0_53,X1_53,X0_51,X1_51) = k9_relat_1(X0_51,X1_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_842,plain,
    ( k7_relset_1(X0_53,X1_53,X0_51,X1_51) = k9_relat_1(X0_51,X1_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_2829,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),X0_51) = k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),X0_51) ),
    inference(superposition,[status(thm)],[c_2822,c_842])).

cnf(c_1490,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k9_relat_1(sK4,X0_51) ),
    inference(superposition,[status(thm)],[c_850,c_842])).

cnf(c_8,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_450,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1493,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_1490,c_450])).

cnf(c_2321,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_2318,c_1493])).

cnf(c_3034,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_2829,c_2321])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_253,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | u1_struct_0(sK2) != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_254,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
    inference(resolution,[status(thm)],[c_1,c_254])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k9_relat_1(k7_relat_1(X0_51,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_51,sK5) ),
    inference(subtyping,[status(esa)],[c_268])).

cnf(c_863,plain,
    ( k9_relat_1(k7_relat_1(X0_51,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_51,sK5)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_1526,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_850,c_863])).

cnf(c_3035,plain,
    ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3034,c_1526])).

cnf(c_3036,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3035])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:48:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.86/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.86/0.98  
% 1.86/0.98  ------  iProver source info
% 1.86/0.98  
% 1.86/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.86/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.86/0.98  git: non_committed_changes: false
% 1.86/0.98  git: last_make_outside_of_git: false
% 1.86/0.98  
% 1.86/0.98  ------ 
% 1.86/0.98  
% 1.86/0.98  ------ Input Options
% 1.86/0.98  
% 1.86/0.98  --out_options                           all
% 1.86/0.98  --tptp_safe_out                         true
% 1.86/0.98  --problem_path                          ""
% 1.86/0.98  --include_path                          ""
% 1.86/0.98  --clausifier                            res/vclausify_rel
% 1.86/0.98  --clausifier_options                    --mode clausify
% 1.86/0.98  --stdin                                 false
% 1.86/0.98  --stats_out                             all
% 1.86/0.98  
% 1.86/0.98  ------ General Options
% 1.86/0.98  
% 1.86/0.98  --fof                                   false
% 1.86/0.98  --time_out_real                         305.
% 1.86/0.98  --time_out_virtual                      -1.
% 1.86/0.98  --symbol_type_check                     false
% 1.86/0.98  --clausify_out                          false
% 1.86/0.98  --sig_cnt_out                           false
% 1.86/0.98  --trig_cnt_out                          false
% 1.86/0.98  --trig_cnt_out_tolerance                1.
% 1.86/0.98  --trig_cnt_out_sk_spl                   false
% 1.86/0.98  --abstr_cl_out                          false
% 1.86/0.98  
% 1.86/0.98  ------ Global Options
% 1.86/0.98  
% 1.86/0.98  --schedule                              default
% 1.86/0.98  --add_important_lit                     false
% 1.86/0.98  --prop_solver_per_cl                    1000
% 1.86/0.98  --min_unsat_core                        false
% 1.86/0.98  --soft_assumptions                      false
% 1.86/0.98  --soft_lemma_size                       3
% 1.86/0.98  --prop_impl_unit_size                   0
% 1.86/0.98  --prop_impl_unit                        []
% 1.86/0.98  --share_sel_clauses                     true
% 1.86/0.98  --reset_solvers                         false
% 1.86/0.98  --bc_imp_inh                            [conj_cone]
% 1.86/0.98  --conj_cone_tolerance                   3.
% 1.86/0.98  --extra_neg_conj                        none
% 1.86/0.98  --large_theory_mode                     true
% 1.86/0.98  --prolific_symb_bound                   200
% 1.86/0.98  --lt_threshold                          2000
% 1.86/0.98  --clause_weak_htbl                      true
% 1.86/0.98  --gc_record_bc_elim                     false
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing Options
% 1.86/0.98  
% 1.86/0.98  --preprocessing_flag                    true
% 1.86/0.98  --time_out_prep_mult                    0.1
% 1.86/0.98  --splitting_mode                        input
% 1.86/0.98  --splitting_grd                         true
% 1.86/0.98  --splitting_cvd                         false
% 1.86/0.98  --splitting_cvd_svl                     false
% 1.86/0.98  --splitting_nvd                         32
% 1.86/0.98  --sub_typing                            true
% 1.86/0.98  --prep_gs_sim                           true
% 1.86/0.98  --prep_unflatten                        true
% 1.86/0.98  --prep_res_sim                          true
% 1.86/0.98  --prep_upred                            true
% 1.86/0.98  --prep_sem_filter                       exhaustive
% 1.86/0.98  --prep_sem_filter_out                   false
% 1.86/0.98  --pred_elim                             true
% 1.86/0.98  --res_sim_input                         true
% 1.86/0.98  --eq_ax_congr_red                       true
% 1.86/0.98  --pure_diseq_elim                       true
% 1.86/0.98  --brand_transform                       false
% 1.86/0.98  --non_eq_to_eq                          false
% 1.86/0.98  --prep_def_merge                        true
% 1.86/0.98  --prep_def_merge_prop_impl              false
% 1.86/0.98  --prep_def_merge_mbd                    true
% 1.86/0.98  --prep_def_merge_tr_red                 false
% 1.86/0.98  --prep_def_merge_tr_cl                  false
% 1.86/0.98  --smt_preprocessing                     true
% 1.86/0.98  --smt_ac_axioms                         fast
% 1.86/0.98  --preprocessed_out                      false
% 1.86/0.98  --preprocessed_stats                    false
% 1.86/0.98  
% 1.86/0.98  ------ Abstraction refinement Options
% 1.86/0.98  
% 1.86/0.98  --abstr_ref                             []
% 1.86/0.98  --abstr_ref_prep                        false
% 1.86/0.98  --abstr_ref_until_sat                   false
% 1.86/0.98  --abstr_ref_sig_restrict                funpre
% 1.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.86/0.98  --abstr_ref_under                       []
% 1.86/0.98  
% 1.86/0.98  ------ SAT Options
% 1.86/0.98  
% 1.86/0.98  --sat_mode                              false
% 1.86/0.98  --sat_fm_restart_options                ""
% 1.86/0.98  --sat_gr_def                            false
% 1.86/0.98  --sat_epr_types                         true
% 1.86/0.98  --sat_non_cyclic_types                  false
% 1.86/0.98  --sat_finite_models                     false
% 1.86/0.98  --sat_fm_lemmas                         false
% 1.86/0.98  --sat_fm_prep                           false
% 1.86/0.98  --sat_fm_uc_incr                        true
% 1.86/0.98  --sat_out_model                         small
% 1.86/0.98  --sat_out_clauses                       false
% 1.86/0.98  
% 1.86/0.98  ------ QBF Options
% 1.86/0.98  
% 1.86/0.98  --qbf_mode                              false
% 1.86/0.98  --qbf_elim_univ                         false
% 1.86/0.98  --qbf_dom_inst                          none
% 1.86/0.98  --qbf_dom_pre_inst                      false
% 1.86/0.98  --qbf_sk_in                             false
% 1.86/0.98  --qbf_pred_elim                         true
% 1.86/0.98  --qbf_split                             512
% 1.86/0.98  
% 1.86/0.98  ------ BMC1 Options
% 1.86/0.98  
% 1.86/0.98  --bmc1_incremental                      false
% 1.86/0.98  --bmc1_axioms                           reachable_all
% 1.86/0.98  --bmc1_min_bound                        0
% 1.86/0.98  --bmc1_max_bound                        -1
% 1.86/0.98  --bmc1_max_bound_default                -1
% 1.86/0.98  --bmc1_symbol_reachability              true
% 1.86/0.98  --bmc1_property_lemmas                  false
% 1.86/0.98  --bmc1_k_induction                      false
% 1.86/0.98  --bmc1_non_equiv_states                 false
% 1.86/0.98  --bmc1_deadlock                         false
% 1.86/0.98  --bmc1_ucm                              false
% 1.86/0.98  --bmc1_add_unsat_core                   none
% 1.86/0.98  --bmc1_unsat_core_children              false
% 1.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.86/0.98  --bmc1_out_stat                         full
% 1.86/0.98  --bmc1_ground_init                      false
% 1.86/0.98  --bmc1_pre_inst_next_state              false
% 1.86/0.98  --bmc1_pre_inst_state                   false
% 1.86/0.98  --bmc1_pre_inst_reach_state             false
% 1.86/0.98  --bmc1_out_unsat_core                   false
% 1.86/0.98  --bmc1_aig_witness_out                  false
% 1.86/0.98  --bmc1_verbose                          false
% 1.86/0.98  --bmc1_dump_clauses_tptp                false
% 1.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.86/0.98  --bmc1_dump_file                        -
% 1.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.86/0.98  --bmc1_ucm_extend_mode                  1
% 1.86/0.98  --bmc1_ucm_init_mode                    2
% 1.86/0.98  --bmc1_ucm_cone_mode                    none
% 1.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.86/0.98  --bmc1_ucm_relax_model                  4
% 1.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.86/0.98  --bmc1_ucm_layered_model                none
% 1.86/0.98  --bmc1_ucm_max_lemma_size               10
% 1.86/0.98  
% 1.86/0.98  ------ AIG Options
% 1.86/0.98  
% 1.86/0.98  --aig_mode                              false
% 1.86/0.98  
% 1.86/0.98  ------ Instantiation Options
% 1.86/0.98  
% 1.86/0.98  --instantiation_flag                    true
% 1.86/0.98  --inst_sos_flag                         false
% 1.86/0.98  --inst_sos_phase                        true
% 1.86/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.86/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.86/0.98  --inst_lit_sel_side                     num_symb
% 1.86/0.98  --inst_solver_per_active                1400
% 1.86/0.98  --inst_solver_calls_frac                1.
% 1.86/0.98  --inst_passive_queue_type               priority_queues
% 1.86/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.86/0.98  --inst_passive_queues_freq              [25;2]
% 1.86/0.98  --inst_dismatching                      true
% 1.86/0.98  --inst_eager_unprocessed_to_passive     true
% 1.86/0.98  --inst_prop_sim_given                   true
% 1.86/0.98  --inst_prop_sim_new                     false
% 1.86/0.98  --inst_subs_new                         false
% 1.86/0.98  --inst_eq_res_simp                      false
% 1.86/0.98  --inst_subs_given                       false
% 1.86/0.98  --inst_orphan_elimination               true
% 1.86/0.98  --inst_learning_loop_flag               true
% 1.86/0.98  --inst_learning_start                   3000
% 1.86/0.98  --inst_learning_factor                  2
% 1.86/0.98  --inst_start_prop_sim_after_learn       3
% 1.86/0.98  --inst_sel_renew                        solver
% 1.86/0.98  --inst_lit_activity_flag                true
% 1.86/0.98  --inst_restr_to_given                   false
% 1.86/0.98  --inst_activity_threshold               500
% 1.86/0.98  --inst_out_proof                        true
% 1.86/0.98  
% 1.86/0.98  ------ Resolution Options
% 1.86/0.98  
% 1.86/0.98  --resolution_flag                       true
% 1.86/0.98  --res_lit_sel                           adaptive
% 1.86/0.98  --res_lit_sel_side                      none
% 1.86/0.98  --res_ordering                          kbo
% 1.86/0.98  --res_to_prop_solver                    active
% 1.86/0.98  --res_prop_simpl_new                    false
% 1.86/0.98  --res_prop_simpl_given                  true
% 1.86/0.98  --res_passive_queue_type                priority_queues
% 1.86/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.98  --res_passive_queues_freq               [15;5]
% 1.86/0.98  --res_forward_subs                      full
% 1.86/0.98  --res_backward_subs                     full
% 1.86/0.98  --res_forward_subs_resolution           true
% 1.86/0.98  --res_backward_subs_resolution          true
% 1.86/0.98  --res_orphan_elimination                true
% 1.86/0.98  --res_time_limit                        2.
% 1.86/0.98  --res_out_proof                         true
% 1.86/0.98  
% 1.86/0.98  ------ Superposition Options
% 1.86/0.98  
% 1.86/0.98  --superposition_flag                    true
% 1.86/0.98  --sup_passive_queue_type                priority_queues
% 1.86/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.98  --demod_completeness_check              fast
% 1.86/0.98  --demod_use_ground                      true
% 1.86/0.98  --sup_to_prop_solver                    passive
% 1.86/0.98  --sup_prop_simpl_new                    true
% 1.86/0.98  --sup_prop_simpl_given                  true
% 1.86/0.98  --sup_fun_splitting                     false
% 1.86/0.98  --sup_smt_interval                      50000
% 1.86/0.98  
% 1.86/0.98  ------ Superposition Simplification Setup
% 1.86/0.98  
% 1.86/0.98  --sup_indices_passive                   []
% 1.86/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_full_bw                           [BwDemod]
% 1.86/0.98  --sup_immed_triv                        [TrivRules]
% 1.86/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_immed_bw_main                     []
% 1.86/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.98  
% 1.86/0.98  ------ Combination Options
% 1.86/0.98  
% 1.86/0.98  --comb_res_mult                         3
% 1.86/0.98  --comb_sup_mult                         2
% 1.86/0.98  --comb_inst_mult                        10
% 1.86/0.98  
% 1.86/0.98  ------ Debug Options
% 1.86/0.98  
% 1.86/0.98  --dbg_backtrace                         false
% 1.86/0.98  --dbg_dump_prop_clauses                 false
% 1.86/0.98  --dbg_dump_prop_clauses_file            -
% 1.86/0.98  --dbg_out_stat                          false
% 1.86/0.98  ------ Parsing...
% 1.86/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.86/0.98  ------ Proving...
% 1.86/0.98  ------ Problem Properties 
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  clauses                                 23
% 1.86/0.98  conjectures                             16
% 1.86/0.98  EPR                                     12
% 1.86/0.98  Horn                                    19
% 1.86/0.98  unary                                   16
% 1.86/0.98  binary                                  2
% 1.86/0.98  lits                                    72
% 1.86/0.98  lits eq                                 5
% 1.86/0.98  fd_pure                                 0
% 1.86/0.98  fd_pseudo                               0
% 1.86/0.98  fd_cond                                 0
% 1.86/0.98  fd_pseudo_cond                          0
% 1.86/0.98  AC symbols                              0
% 1.86/0.98  
% 1.86/0.98  ------ Schedule dynamic 5 is on 
% 1.86/0.98  
% 1.86/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  ------ 
% 1.86/0.98  Current options:
% 1.86/0.98  ------ 
% 1.86/0.98  
% 1.86/0.98  ------ Input Options
% 1.86/0.98  
% 1.86/0.98  --out_options                           all
% 1.86/0.98  --tptp_safe_out                         true
% 1.86/0.98  --problem_path                          ""
% 1.86/0.98  --include_path                          ""
% 1.86/0.98  --clausifier                            res/vclausify_rel
% 1.86/0.98  --clausifier_options                    --mode clausify
% 1.86/0.98  --stdin                                 false
% 1.86/0.98  --stats_out                             all
% 1.86/0.98  
% 1.86/0.98  ------ General Options
% 1.86/0.98  
% 1.86/0.98  --fof                                   false
% 1.86/0.98  --time_out_real                         305.
% 1.86/0.98  --time_out_virtual                      -1.
% 1.86/0.98  --symbol_type_check                     false
% 1.86/0.98  --clausify_out                          false
% 1.86/0.98  --sig_cnt_out                           false
% 1.86/0.98  --trig_cnt_out                          false
% 1.86/0.98  --trig_cnt_out_tolerance                1.
% 1.86/0.98  --trig_cnt_out_sk_spl                   false
% 1.86/0.98  --abstr_cl_out                          false
% 1.86/0.98  
% 1.86/0.98  ------ Global Options
% 1.86/0.98  
% 1.86/0.98  --schedule                              default
% 1.86/0.98  --add_important_lit                     false
% 1.86/0.98  --prop_solver_per_cl                    1000
% 1.86/0.98  --min_unsat_core                        false
% 1.86/0.98  --soft_assumptions                      false
% 1.86/0.98  --soft_lemma_size                       3
% 1.86/0.98  --prop_impl_unit_size                   0
% 1.86/0.98  --prop_impl_unit                        []
% 1.86/0.98  --share_sel_clauses                     true
% 1.86/0.98  --reset_solvers                         false
% 1.86/0.98  --bc_imp_inh                            [conj_cone]
% 1.86/0.98  --conj_cone_tolerance                   3.
% 1.86/0.98  --extra_neg_conj                        none
% 1.86/0.98  --large_theory_mode                     true
% 1.86/0.98  --prolific_symb_bound                   200
% 1.86/0.98  --lt_threshold                          2000
% 1.86/0.98  --clause_weak_htbl                      true
% 1.86/0.98  --gc_record_bc_elim                     false
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing Options
% 1.86/0.98  
% 1.86/0.98  --preprocessing_flag                    true
% 1.86/0.98  --time_out_prep_mult                    0.1
% 1.86/0.98  --splitting_mode                        input
% 1.86/0.98  --splitting_grd                         true
% 1.86/0.98  --splitting_cvd                         false
% 1.86/0.98  --splitting_cvd_svl                     false
% 1.86/0.98  --splitting_nvd                         32
% 1.86/0.98  --sub_typing                            true
% 1.86/0.98  --prep_gs_sim                           true
% 1.86/0.98  --prep_unflatten                        true
% 1.86/0.98  --prep_res_sim                          true
% 1.86/0.98  --prep_upred                            true
% 1.86/0.98  --prep_sem_filter                       exhaustive
% 1.86/0.98  --prep_sem_filter_out                   false
% 1.86/0.98  --pred_elim                             true
% 1.86/0.98  --res_sim_input                         true
% 1.86/0.98  --eq_ax_congr_red                       true
% 1.86/0.98  --pure_diseq_elim                       true
% 1.86/0.98  --brand_transform                       false
% 1.86/0.98  --non_eq_to_eq                          false
% 1.86/0.98  --prep_def_merge                        true
% 1.86/0.98  --prep_def_merge_prop_impl              false
% 1.86/0.98  --prep_def_merge_mbd                    true
% 1.86/0.98  --prep_def_merge_tr_red                 false
% 1.86/0.98  --prep_def_merge_tr_cl                  false
% 1.86/0.98  --smt_preprocessing                     true
% 1.86/0.98  --smt_ac_axioms                         fast
% 1.86/0.98  --preprocessed_out                      false
% 1.86/0.98  --preprocessed_stats                    false
% 1.86/0.98  
% 1.86/0.98  ------ Abstraction refinement Options
% 1.86/0.98  
% 1.86/0.98  --abstr_ref                             []
% 1.86/0.98  --abstr_ref_prep                        false
% 1.86/0.98  --abstr_ref_until_sat                   false
% 1.86/0.98  --abstr_ref_sig_restrict                funpre
% 1.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.86/0.98  --abstr_ref_under                       []
% 1.86/0.98  
% 1.86/0.98  ------ SAT Options
% 1.86/0.98  
% 1.86/0.98  --sat_mode                              false
% 1.86/0.98  --sat_fm_restart_options                ""
% 1.86/0.98  --sat_gr_def                            false
% 1.86/0.98  --sat_epr_types                         true
% 1.86/0.98  --sat_non_cyclic_types                  false
% 1.86/0.98  --sat_finite_models                     false
% 1.86/0.98  --sat_fm_lemmas                         false
% 1.86/0.98  --sat_fm_prep                           false
% 1.86/0.98  --sat_fm_uc_incr                        true
% 1.86/0.98  --sat_out_model                         small
% 1.86/0.98  --sat_out_clauses                       false
% 1.86/0.98  
% 1.86/0.98  ------ QBF Options
% 1.86/0.98  
% 1.86/0.98  --qbf_mode                              false
% 1.86/0.98  --qbf_elim_univ                         false
% 1.86/0.98  --qbf_dom_inst                          none
% 1.86/0.98  --qbf_dom_pre_inst                      false
% 1.86/0.98  --qbf_sk_in                             false
% 1.86/0.98  --qbf_pred_elim                         true
% 1.86/0.98  --qbf_split                             512
% 1.86/0.98  
% 1.86/0.98  ------ BMC1 Options
% 1.86/0.98  
% 1.86/0.98  --bmc1_incremental                      false
% 1.86/0.98  --bmc1_axioms                           reachable_all
% 1.86/0.98  --bmc1_min_bound                        0
% 1.86/0.98  --bmc1_max_bound                        -1
% 1.86/0.98  --bmc1_max_bound_default                -1
% 1.86/0.98  --bmc1_symbol_reachability              true
% 1.86/0.98  --bmc1_property_lemmas                  false
% 1.86/0.98  --bmc1_k_induction                      false
% 1.86/0.98  --bmc1_non_equiv_states                 false
% 1.86/0.98  --bmc1_deadlock                         false
% 1.86/0.98  --bmc1_ucm                              false
% 1.86/0.98  --bmc1_add_unsat_core                   none
% 1.86/0.98  --bmc1_unsat_core_children              false
% 1.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.86/0.98  --bmc1_out_stat                         full
% 1.86/0.98  --bmc1_ground_init                      false
% 1.86/0.98  --bmc1_pre_inst_next_state              false
% 1.86/0.98  --bmc1_pre_inst_state                   false
% 1.86/0.98  --bmc1_pre_inst_reach_state             false
% 1.86/0.98  --bmc1_out_unsat_core                   false
% 1.86/0.98  --bmc1_aig_witness_out                  false
% 1.86/0.98  --bmc1_verbose                          false
% 1.86/0.98  --bmc1_dump_clauses_tptp                false
% 1.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.86/0.98  --bmc1_dump_file                        -
% 1.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.86/0.98  --bmc1_ucm_extend_mode                  1
% 1.86/0.98  --bmc1_ucm_init_mode                    2
% 1.86/0.98  --bmc1_ucm_cone_mode                    none
% 1.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.86/0.98  --bmc1_ucm_relax_model                  4
% 1.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.86/0.98  --bmc1_ucm_layered_model                none
% 1.86/0.98  --bmc1_ucm_max_lemma_size               10
% 1.86/0.98  
% 1.86/0.98  ------ AIG Options
% 1.86/0.98  
% 1.86/0.98  --aig_mode                              false
% 1.86/0.98  
% 1.86/0.98  ------ Instantiation Options
% 1.86/0.98  
% 1.86/0.98  --instantiation_flag                    true
% 1.86/0.98  --inst_sos_flag                         false
% 1.86/0.98  --inst_sos_phase                        true
% 1.86/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.86/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.86/0.98  --inst_lit_sel_side                     none
% 1.86/0.98  --inst_solver_per_active                1400
% 1.86/0.98  --inst_solver_calls_frac                1.
% 1.86/0.98  --inst_passive_queue_type               priority_queues
% 1.86/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.86/0.98  --inst_passive_queues_freq              [25;2]
% 1.86/0.98  --inst_dismatching                      true
% 1.86/0.98  --inst_eager_unprocessed_to_passive     true
% 1.86/0.98  --inst_prop_sim_given                   true
% 1.86/0.98  --inst_prop_sim_new                     false
% 1.86/0.98  --inst_subs_new                         false
% 1.86/0.98  --inst_eq_res_simp                      false
% 1.86/0.98  --inst_subs_given                       false
% 1.86/0.98  --inst_orphan_elimination               true
% 1.86/0.98  --inst_learning_loop_flag               true
% 1.86/0.98  --inst_learning_start                   3000
% 1.86/0.98  --inst_learning_factor                  2
% 1.86/0.98  --inst_start_prop_sim_after_learn       3
% 1.86/0.98  --inst_sel_renew                        solver
% 1.86/0.98  --inst_lit_activity_flag                true
% 1.86/0.98  --inst_restr_to_given                   false
% 1.86/0.98  --inst_activity_threshold               500
% 1.86/0.98  --inst_out_proof                        true
% 1.86/0.98  
% 1.86/0.98  ------ Resolution Options
% 1.86/0.98  
% 1.86/0.98  --resolution_flag                       false
% 1.86/0.98  --res_lit_sel                           adaptive
% 1.86/0.98  --res_lit_sel_side                      none
% 1.86/0.98  --res_ordering                          kbo
% 1.86/0.98  --res_to_prop_solver                    active
% 1.86/0.98  --res_prop_simpl_new                    false
% 1.86/0.98  --res_prop_simpl_given                  true
% 1.86/0.98  --res_passive_queue_type                priority_queues
% 1.86/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.98  --res_passive_queues_freq               [15;5]
% 1.86/0.98  --res_forward_subs                      full
% 1.86/0.98  --res_backward_subs                     full
% 1.86/0.98  --res_forward_subs_resolution           true
% 1.86/0.98  --res_backward_subs_resolution          true
% 1.86/0.98  --res_orphan_elimination                true
% 1.86/0.98  --res_time_limit                        2.
% 1.86/0.98  --res_out_proof                         true
% 1.86/0.98  
% 1.86/0.98  ------ Superposition Options
% 1.86/0.98  
% 1.86/0.98  --superposition_flag                    true
% 1.86/0.98  --sup_passive_queue_type                priority_queues
% 1.86/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.98  --demod_completeness_check              fast
% 1.86/0.98  --demod_use_ground                      true
% 1.86/0.98  --sup_to_prop_solver                    passive
% 1.86/0.98  --sup_prop_simpl_new                    true
% 1.86/0.98  --sup_prop_simpl_given                  true
% 1.86/0.98  --sup_fun_splitting                     false
% 1.86/0.98  --sup_smt_interval                      50000
% 1.86/0.98  
% 1.86/0.98  ------ Superposition Simplification Setup
% 1.86/0.98  
% 1.86/0.98  --sup_indices_passive                   []
% 1.86/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_full_bw                           [BwDemod]
% 1.86/0.98  --sup_immed_triv                        [TrivRules]
% 1.86/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_immed_bw_main                     []
% 1.86/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.98  
% 1.86/0.98  ------ Combination Options
% 1.86/0.98  
% 1.86/0.98  --comb_res_mult                         3
% 1.86/0.98  --comb_sup_mult                         2
% 1.86/0.98  --comb_inst_mult                        10
% 1.86/0.98  
% 1.86/0.98  ------ Debug Options
% 1.86/0.98  
% 1.86/0.98  --dbg_backtrace                         false
% 1.86/0.98  --dbg_dump_prop_clauses                 false
% 1.86/0.98  --dbg_dump_prop_clauses_file            -
% 1.86/0.98  --dbg_out_stat                          false
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  ------ Proving...
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  % SZS status Theorem for theBenchmark.p
% 1.86/0.98  
% 1.86/0.98   Resolution empty clause
% 1.86/0.98  
% 1.86/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  fof(f7,conjecture,(
% 1.86/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 1.86/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f8,negated_conjecture,(
% 1.86/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 1.86/0.98    inference(negated_conjecture,[],[f7])).
% 1.86/0.98  
% 1.86/0.98  fof(f18,plain,(
% 1.86/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.86/0.98    inference(ennf_transformation,[],[f8])).
% 1.86/0.98  
% 1.86/0.98  fof(f19,plain,(
% 1.86/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.86/0.98    inference(flattening,[],[f18])).
% 1.86/0.98  
% 1.86/0.98  fof(f25,plain,(
% 1.86/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5) & r1_tarski(sK5,u1_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 1.86/0.98    introduced(choice_axiom,[])).
% 1.86/0.98  
% 1.86/0.98  fof(f24,plain,(
% 1.86/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.86/0.98    introduced(choice_axiom,[])).
% 1.86/0.98  
% 1.86/0.98  fof(f23,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.86/0.98    introduced(choice_axiom,[])).
% 1.86/0.98  
% 1.86/0.98  fof(f22,plain,(
% 1.86/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.86/0.98    introduced(choice_axiom,[])).
% 1.86/0.98  
% 1.86/0.98  fof(f21,plain,(
% 1.86/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.86/0.98    introduced(choice_axiom,[])).
% 1.86/0.98  
% 1.86/0.98  fof(f20,plain,(
% 1.86/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.86/0.98    introduced(choice_axiom,[])).
% 1.86/0.98  
% 1.86/0.98  fof(f26,plain,(
% 1.86/0.98    (((((k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.86/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f25,f24,f23,f22,f21,f20])).
% 1.86/0.98  
% 1.86/0.98  fof(f42,plain,(
% 1.86/0.98    m1_pre_topc(sK2,sK0)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f44,plain,(
% 1.86/0.98    m1_pre_topc(sK3,sK0)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f47,plain,(
% 1.86/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f5,axiom,(
% 1.86/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 1.86/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f14,plain,(
% 1.86/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.86/0.98    inference(ennf_transformation,[],[f5])).
% 1.86/0.98  
% 1.86/0.98  fof(f15,plain,(
% 1.86/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.86/0.98    inference(flattening,[],[f14])).
% 1.86/0.98  
% 1.86/0.98  fof(f31,plain,(
% 1.86/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f15])).
% 1.86/0.98  
% 1.86/0.98  fof(f38,plain,(
% 1.86/0.98    ~v2_struct_0(sK1)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f39,plain,(
% 1.86/0.98    v2_pre_topc(sK1)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f40,plain,(
% 1.86/0.98    l1_pre_topc(sK1)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f45,plain,(
% 1.86/0.98    v1_funct_1(sK4)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f46,plain,(
% 1.86/0.98    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f4,axiom,(
% 1.86/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 1.86/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f12,plain,(
% 1.86/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.86/0.98    inference(ennf_transformation,[],[f4])).
% 1.86/0.98  
% 1.86/0.98  fof(f13,plain,(
% 1.86/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.86/0.98    inference(flattening,[],[f12])).
% 1.86/0.98  
% 1.86/0.98  fof(f30,plain,(
% 1.86/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f13])).
% 1.86/0.98  
% 1.86/0.98  fof(f35,plain,(
% 1.86/0.98    ~v2_struct_0(sK0)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f36,plain,(
% 1.86/0.98    v2_pre_topc(sK0)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f37,plain,(
% 1.86/0.98    l1_pre_topc(sK0)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f48,plain,(
% 1.86/0.98    m1_pre_topc(sK2,sK3)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f6,axiom,(
% 1.86/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.86/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f16,plain,(
% 1.86/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.86/0.98    inference(ennf_transformation,[],[f6])).
% 1.86/0.98  
% 1.86/0.98  fof(f17,plain,(
% 1.86/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.86/0.98    inference(flattening,[],[f16])).
% 1.86/0.98  
% 1.86/0.98  fof(f34,plain,(
% 1.86/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f17])).
% 1.86/0.98  
% 1.86/0.98  fof(f3,axiom,(
% 1.86/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.86/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f11,plain,(
% 1.86/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.98    inference(ennf_transformation,[],[f3])).
% 1.86/0.98  
% 1.86/0.98  fof(f29,plain,(
% 1.86/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.98    inference(cnf_transformation,[],[f11])).
% 1.86/0.98  
% 1.86/0.98  fof(f51,plain,(
% 1.86/0.98    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f2,axiom,(
% 1.86/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.86/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f10,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.98    inference(ennf_transformation,[],[f2])).
% 1.86/0.98  
% 1.86/0.98  fof(f28,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.98    inference(cnf_transformation,[],[f10])).
% 1.86/0.98  
% 1.86/0.98  fof(f1,axiom,(
% 1.86/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 1.86/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f9,plain,(
% 1.86/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.86/0.98    inference(ennf_transformation,[],[f1])).
% 1.86/0.98  
% 1.86/0.98  fof(f27,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f9])).
% 1.86/0.98  
% 1.86/0.98  fof(f50,plain,(
% 1.86/0.98    r1_tarski(sK5,u1_struct_0(sK2))),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  cnf(c_17,negated_conjecture,
% 1.86/0.98      ( m1_pre_topc(sK2,sK0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_442,negated_conjecture,
% 1.86/0.98      ( m1_pre_topc(sK2,sK0) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_855,plain,
% 1.86/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_15,negated_conjecture,
% 1.86/0.98      ( m1_pre_topc(sK3,sK0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_444,negated_conjecture,
% 1.86/0.98      ( m1_pre_topc(sK3,sK0) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_853,plain,
% 1.86/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_12,negated_conjecture,
% 1.86/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.86/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_447,negated_conjecture,
% 1.86/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_850,plain,
% 1.86/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_4,plain,
% 1.86/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.86/0.98      | ~ m1_pre_topc(X3,X1)
% 1.86/0.98      | ~ m1_pre_topc(X3,X4)
% 1.86/0.98      | ~ m1_pre_topc(X1,X4)
% 1.86/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.86/0.98      | v2_struct_0(X4)
% 1.86/0.98      | v2_struct_0(X2)
% 1.86/0.98      | ~ v2_pre_topc(X2)
% 1.86/0.98      | ~ v2_pre_topc(X4)
% 1.86/0.98      | ~ l1_pre_topc(X2)
% 1.86/0.98      | ~ l1_pre_topc(X4)
% 1.86/0.98      | ~ v1_funct_1(X0)
% 1.86/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_454,plain,
% 1.86/0.98      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 1.86/0.98      | ~ m1_pre_topc(X2_55,X3_55)
% 1.86/0.98      | ~ m1_pre_topc(X0_55,X3_55)
% 1.86/0.98      | ~ m1_pre_topc(X2_55,X0_55)
% 1.86/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.86/0.98      | v2_struct_0(X3_55)
% 1.86/0.98      | v2_struct_0(X1_55)
% 1.86/0.98      | ~ v2_pre_topc(X1_55)
% 1.86/0.98      | ~ v2_pre_topc(X3_55)
% 1.86/0.98      | ~ l1_pre_topc(X1_55)
% 1.86/0.98      | ~ l1_pre_topc(X3_55)
% 1.86/0.98      | ~ v1_funct_1(X0_51)
% 1.86/0.98      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_51,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_51) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_844,plain,
% 1.86/0.98      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_51,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_51)
% 1.86/0.98      | v1_funct_2(X0_51,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 1.86/0.98      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 1.86/0.98      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 1.86/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 1.86/0.98      | v2_struct_0(X3_55) = iProver_top
% 1.86/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.86/0.98      | v2_pre_topc(X3_55) != iProver_top
% 1.86/0.98      | v2_pre_topc(X1_55) != iProver_top
% 1.86/0.98      | l1_pre_topc(X3_55) != iProver_top
% 1.86/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.86/0.98      | v1_funct_1(X0_51) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1932,plain,
% 1.86/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 1.86/0.98      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.86/0.98      | m1_pre_topc(sK3,X1_55) != iProver_top
% 1.86/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.86/0.98      | v2_struct_0(sK1) = iProver_top
% 1.86/0.98      | v2_pre_topc(X1_55) != iProver_top
% 1.86/0.98      | v2_pre_topc(sK1) != iProver_top
% 1.86/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.86/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.86/0.98      | v1_funct_1(sK4) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_850,c_844]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_21,negated_conjecture,
% 1.86/0.98      ( ~ v2_struct_0(sK1) ),
% 1.86/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_28,plain,
% 1.86/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_20,negated_conjecture,
% 1.86/0.98      ( v2_pre_topc(sK1) ),
% 1.86/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_29,plain,
% 1.86/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_19,negated_conjecture,
% 1.86/0.98      ( l1_pre_topc(sK1) ),
% 1.86/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_30,plain,
% 1.86/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_14,negated_conjecture,
% 1.86/0.98      ( v1_funct_1(sK4) ),
% 1.86/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_35,plain,
% 1.86/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_13,negated_conjecture,
% 1.86/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 1.86/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_36,plain,
% 1.86/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2114,plain,
% 1.86/0.98      ( v2_pre_topc(X1_55) != iProver_top
% 1.86/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 1.86/0.98      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.86/0.98      | m1_pre_topc(sK3,X1_55) != iProver_top
% 1.86/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.86/0.98      | l1_pre_topc(X1_55) != iProver_top ),
% 1.86/0.98      inference(global_propositional_subsumption,
% 1.86/0.98                [status(thm)],
% 1.86/0.98                [c_1932,c_28,c_29,c_30,c_35,c_36]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2115,plain,
% 1.86/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 1.86/0.98      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.86/0.98      | m1_pre_topc(sK3,X1_55) != iProver_top
% 1.86/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.86/0.98      | v2_pre_topc(X1_55) != iProver_top
% 1.86/0.98      | l1_pre_topc(X1_55) != iProver_top ),
% 1.86/0.98      inference(renaming,[status(thm)],[c_2114]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_3,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.98      | ~ v1_funct_1(X0)
% 1.86/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 1.86/0.98      inference(cnf_transformation,[],[f30]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_455,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 1.86/0.98      | ~ v1_funct_1(X0_51)
% 1.86/0.98      | k2_partfun1(X0_53,X1_53,X0_51,X2_53) = k7_relat_1(X0_51,X2_53) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_843,plain,
% 1.86/0.98      ( k2_partfun1(X0_53,X1_53,X0_51,X2_53) = k7_relat_1(X0_51,X2_53)
% 1.86/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 1.86/0.98      | v1_funct_1(X0_51) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1606,plain,
% 1.86/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 1.86/0.98      | v1_funct_1(sK4) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_850,c_843]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1083,plain,
% 1.86/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 1.86/0.98      | ~ v1_funct_1(sK4)
% 1.86/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 1.86/0.98      inference(instantiation,[status(thm)],[c_455]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2043,plain,
% 1.86/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 1.86/0.98      inference(global_propositional_subsumption,
% 1.86/0.98                [status(thm)],
% 1.86/0.98                [c_1606,c_14,c_12,c_1083]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2120,plain,
% 1.86/0.98      ( k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
% 1.86/0.98      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 1.86/0.98      | m1_pre_topc(X1_55,sK3) != iProver_top
% 1.86/0.98      | m1_pre_topc(sK3,X0_55) != iProver_top
% 1.86/0.98      | v2_struct_0(X0_55) = iProver_top
% 1.86/0.98      | v2_pre_topc(X0_55) != iProver_top
% 1.86/0.98      | l1_pre_topc(X0_55) != iProver_top ),
% 1.86/0.98      inference(demodulation,[status(thm)],[c_2115,c_2043]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2131,plain,
% 1.86/0.98      ( k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55))
% 1.86/0.98      | m1_pre_topc(X0_55,sK0) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top
% 1.86/0.98      | v2_struct_0(sK0) = iProver_top
% 1.86/0.98      | v2_pre_topc(sK0) != iProver_top
% 1.86/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_853,c_2120]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_24,negated_conjecture,
% 1.86/0.98      ( ~ v2_struct_0(sK0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_25,plain,
% 1.86/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_23,negated_conjecture,
% 1.86/0.98      ( v2_pre_topc(sK0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_26,plain,
% 1.86/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_22,negated_conjecture,
% 1.86/0.98      ( l1_pre_topc(sK0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_27,plain,
% 1.86/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2136,plain,
% 1.86/0.98      ( m1_pre_topc(X0_55,sK3) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,sK0) != iProver_top
% 1.86/0.98      | k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55)) ),
% 1.86/0.98      inference(global_propositional_subsumption,
% 1.86/0.98                [status(thm)],
% 1.86/0.98                [c_2131,c_25,c_26,c_27]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2137,plain,
% 1.86/0.98      ( k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55))
% 1.86/0.98      | m1_pre_topc(X0_55,sK0) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 1.86/0.98      inference(renaming,[status(thm)],[c_2136]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2146,plain,
% 1.86/0.98      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 1.86/0.98      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_855,c_2137]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_11,negated_conjecture,
% 1.86/0.98      ( m1_pre_topc(sK2,sK3) ),
% 1.86/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_38,plain,
% 1.86/0.98      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2318,plain,
% 1.86/0.98      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 1.86/0.98      inference(global_propositional_subsumption,[status(thm)],[c_2146,c_38]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_5,plain,
% 1.86/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.86/0.98      | ~ m1_pre_topc(X3,X4)
% 1.86/0.98      | ~ m1_pre_topc(X1,X4)
% 1.86/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.86/0.98      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 1.86/0.98      | v2_struct_0(X4)
% 1.86/0.98      | v2_struct_0(X2)
% 1.86/0.98      | ~ v2_pre_topc(X2)
% 1.86/0.98      | ~ v2_pre_topc(X4)
% 1.86/0.98      | ~ l1_pre_topc(X2)
% 1.86/0.98      | ~ l1_pre_topc(X4)
% 1.86/0.98      | ~ v1_funct_1(X0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f34]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_453,plain,
% 1.86/0.98      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 1.86/0.98      | ~ m1_pre_topc(X2_55,X3_55)
% 1.86/0.98      | ~ m1_pre_topc(X0_55,X3_55)
% 1.86/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 1.86/0.98      | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 1.86/0.98      | v2_struct_0(X3_55)
% 1.86/0.98      | v2_struct_0(X1_55)
% 1.86/0.98      | ~ v2_pre_topc(X1_55)
% 1.86/0.98      | ~ v2_pre_topc(X3_55)
% 1.86/0.98      | ~ l1_pre_topc(X1_55)
% 1.86/0.98      | ~ l1_pre_topc(X3_55)
% 1.86/0.98      | ~ v1_funct_1(X0_51) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_845,plain,
% 1.86/0.98      ( v1_funct_2(X0_51,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 1.86/0.98      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 1.86/0.98      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 1.86/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 1.86/0.98      | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
% 1.86/0.98      | v2_struct_0(X3_55) = iProver_top
% 1.86/0.98      | v2_struct_0(X1_55) = iProver_top
% 1.86/0.98      | v2_pre_topc(X3_55) != iProver_top
% 1.86/0.98      | v2_pre_topc(X1_55) != iProver_top
% 1.86/0.98      | l1_pre_topc(X3_55) != iProver_top
% 1.86/0.98      | l1_pre_topc(X1_55) != iProver_top
% 1.86/0.98      | v1_funct_1(X0_51) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2322,plain,
% 1.86/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 1.86/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 1.86/0.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 1.86/0.98      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 1.86/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.86/0.98      | v2_struct_0(sK0) = iProver_top
% 1.86/0.98      | v2_struct_0(sK1) = iProver_top
% 1.86/0.98      | v2_pre_topc(sK0) != iProver_top
% 1.86/0.98      | v2_pre_topc(sK1) != iProver_top
% 1.86/0.98      | l1_pre_topc(sK0) != iProver_top
% 1.86/0.98      | l1_pre_topc(sK1) != iProver_top
% 1.86/0.98      | v1_funct_1(sK4) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_2318,c_845]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_32,plain,
% 1.86/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_34,plain,
% 1.86/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_37,plain,
% 1.86/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2822,plain,
% 1.86/0.98      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 1.86/0.98      inference(global_propositional_subsumption,
% 1.86/0.98                [status(thm)],
% 1.86/0.98                [c_2322,c_25,c_26,c_27,c_28,c_29,c_30,c_32,c_34,c_35,c_36,c_37]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.86/0.98      inference(cnf_transformation,[],[f29]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_456,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 1.86/0.98      | k7_relset_1(X0_53,X1_53,X0_51,X1_51) = k9_relat_1(X0_51,X1_51) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_842,plain,
% 1.86/0.98      ( k7_relset_1(X0_53,X1_53,X0_51,X1_51) = k9_relat_1(X0_51,X1_51)
% 1.86/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2829,plain,
% 1.86/0.98      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),X0_51) = k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),X0_51) ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_2822,c_842]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1490,plain,
% 1.86/0.98      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k9_relat_1(sK4,X0_51) ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_850,c_842]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_8,negated_conjecture,
% 1.86/0.98      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 1.86/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_450,negated_conjecture,
% 1.86/0.98      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1493,plain,
% 1.86/0.98      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
% 1.86/0.98      inference(demodulation,[status(thm)],[c_1490,c_450]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2321,plain,
% 1.86/0.98      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 1.86/0.98      inference(demodulation,[status(thm)],[c_2318,c_1493]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_3034,plain,
% 1.86/0.98      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 1.86/0.98      inference(demodulation,[status(thm)],[c_2829,c_2321]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f28]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_0,plain,
% 1.86/0.98      ( ~ r1_tarski(X0,X1)
% 1.86/0.98      | ~ v1_relat_1(X2)
% 1.86/0.98      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f27]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_9,negated_conjecture,
% 1.86/0.98      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 1.86/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_253,plain,
% 1.86/0.98      ( ~ v1_relat_1(X0)
% 1.86/0.98      | k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 1.86/0.98      | u1_struct_0(sK2) != X1
% 1.86/0.98      | sK5 != X2 ),
% 1.86/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_254,plain,
% 1.86/0.98      ( ~ v1_relat_1(X0)
% 1.86/0.98      | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
% 1.86/0.98      inference(unflattening,[status(thm)],[c_253]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_268,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.98      | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
% 1.86/0.98      inference(resolution,[status(thm)],[c_1,c_254]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_434,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 1.86/0.98      | k9_relat_1(k7_relat_1(X0_51,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_51,sK5) ),
% 1.86/0.98      inference(subtyping,[status(esa)],[c_268]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_863,plain,
% 1.86/0.98      ( k9_relat_1(k7_relat_1(X0_51,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_51,sK5)
% 1.86/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1526,plain,
% 1.86/0.98      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_850,c_863]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_3035,plain,
% 1.86/0.98      ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
% 1.86/0.98      inference(light_normalisation,[status(thm)],[c_3034,c_1526]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_3036,plain,
% 1.86/0.98      ( $false ),
% 1.86/0.98      inference(equality_resolution_simp,[status(thm)],[c_3035]) ).
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  ------                               Statistics
% 1.86/0.98  
% 1.86/0.98  ------ General
% 1.86/0.98  
% 1.86/0.98  abstr_ref_over_cycles:                  0
% 1.86/0.98  abstr_ref_under_cycles:                 0
% 1.86/0.98  gc_basic_clause_elim:                   0
% 1.86/0.98  forced_gc_time:                         0
% 1.86/0.98  parsing_time:                           0.009
% 1.86/0.98  unif_index_cands_time:                  0.
% 1.86/0.98  unif_index_add_time:                    0.
% 1.86/0.98  orderings_time:                         0.
% 1.86/0.98  out_proof_time:                         0.008
% 1.86/0.98  total_time:                             0.146
% 1.86/0.98  num_of_symbols:                         59
% 1.86/0.98  num_of_terms:                           3011
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing
% 1.86/0.98  
% 1.86/0.98  num_of_splits:                          0
% 1.86/0.98  num_of_split_atoms:                     0
% 1.86/0.98  num_of_reused_defs:                     0
% 1.86/0.98  num_eq_ax_congr_red:                    31
% 1.86/0.98  num_of_sem_filtered_clauses:            1
% 1.86/0.98  num_of_subtypes:                        5
% 1.86/0.98  monotx_restored_types:                  0
% 1.86/0.98  sat_num_of_epr_types:                   0
% 1.86/0.98  sat_num_of_non_cyclic_types:            0
% 1.86/0.98  sat_guarded_non_collapsed_types:        0
% 1.86/0.98  num_pure_diseq_elim:                    0
% 1.86/0.98  simp_replaced_by:                       0
% 1.86/0.98  res_preprocessed:                       115
% 1.86/0.98  prep_upred:                             0
% 1.86/0.98  prep_unflattend:                        2
% 1.86/0.98  smt_new_axioms:                         0
% 1.86/0.98  pred_elim_cands:                        7
% 1.86/0.98  pred_elim:                              2
% 1.86/0.98  pred_elim_cl:                           2
% 1.86/0.98  pred_elim_cycles:                       4
% 1.86/0.98  merged_defs:                            0
% 1.86/0.98  merged_defs_ncl:                        0
% 1.86/0.98  bin_hyper_res:                          0
% 1.86/0.98  prep_cycles:                            4
% 1.86/0.98  pred_elim_time:                         0.001
% 1.86/0.98  splitting_time:                         0.
% 1.86/0.98  sem_filter_time:                        0.
% 1.86/0.98  monotx_time:                            0.
% 1.86/0.98  subtype_inf_time:                       0.001
% 1.86/0.98  
% 1.86/0.98  ------ Problem properties
% 1.86/0.98  
% 1.86/0.98  clauses:                                23
% 1.86/0.98  conjectures:                            16
% 1.86/0.98  epr:                                    12
% 1.86/0.98  horn:                                   19
% 1.86/0.98  ground:                                 16
% 1.86/0.98  unary:                                  16
% 1.86/0.98  binary:                                 2
% 1.86/0.98  lits:                                   72
% 1.86/0.98  lits_eq:                                5
% 1.86/0.98  fd_pure:                                0
% 1.86/0.98  fd_pseudo:                              0
% 1.86/0.98  fd_cond:                                0
% 1.86/0.98  fd_pseudo_cond:                         0
% 1.86/0.98  ac_symbols:                             0
% 1.86/0.98  
% 1.86/0.98  ------ Propositional Solver
% 1.86/0.98  
% 1.86/0.98  prop_solver_calls:                      28
% 1.86/0.98  prop_fast_solver_calls:                 924
% 1.86/0.98  smt_solver_calls:                       0
% 1.86/0.98  smt_fast_solver_calls:                  0
% 1.86/0.98  prop_num_of_clauses:                    978
% 1.86/0.98  prop_preprocess_simplified:             3379
% 1.86/0.98  prop_fo_subsumed:                       56
% 1.86/0.98  prop_solver_time:                       0.
% 1.86/0.98  smt_solver_time:                        0.
% 1.86/0.98  smt_fast_solver_time:                   0.
% 1.86/0.98  prop_fast_solver_time:                  0.
% 1.86/0.98  prop_unsat_core_time:                   0.
% 1.86/0.98  
% 1.86/0.98  ------ QBF
% 1.86/0.98  
% 1.86/0.98  qbf_q_res:                              0
% 1.86/0.98  qbf_num_tautologies:                    0
% 1.86/0.98  qbf_prep_cycles:                        0
% 1.86/0.98  
% 1.86/0.98  ------ BMC1
% 1.86/0.98  
% 1.86/0.98  bmc1_current_bound:                     -1
% 1.86/0.98  bmc1_last_solved_bound:                 -1
% 1.86/0.98  bmc1_unsat_core_size:                   -1
% 1.86/0.98  bmc1_unsat_core_parents_size:           -1
% 1.86/0.98  bmc1_merge_next_fun:                    0
% 1.86/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.86/0.98  
% 1.86/0.98  ------ Instantiation
% 1.86/0.98  
% 1.86/0.98  inst_num_of_clauses:                    306
% 1.86/0.98  inst_num_in_passive:                    76
% 1.86/0.98  inst_num_in_active:                     208
% 1.86/0.98  inst_num_in_unprocessed:                22
% 1.86/0.98  inst_num_of_loops:                      220
% 1.86/0.98  inst_num_of_learning_restarts:          0
% 1.86/0.98  inst_num_moves_active_passive:          7
% 1.86/0.98  inst_lit_activity:                      0
% 1.86/0.98  inst_lit_activity_moves:                0
% 1.86/0.98  inst_num_tautologies:                   0
% 1.86/0.98  inst_num_prop_implied:                  0
% 1.86/0.98  inst_num_existing_simplified:           0
% 1.86/0.98  inst_num_eq_res_simplified:             0
% 1.86/0.98  inst_num_child_elim:                    0
% 1.86/0.98  inst_num_of_dismatching_blockings:      72
% 1.86/0.98  inst_num_of_non_proper_insts:           265
% 1.86/0.98  inst_num_of_duplicates:                 0
% 1.86/0.98  inst_inst_num_from_inst_to_res:         0
% 1.86/0.98  inst_dismatching_checking_time:         0.
% 1.86/0.98  
% 1.86/0.98  ------ Resolution
% 1.86/0.98  
% 1.86/0.98  res_num_of_clauses:                     0
% 1.86/0.98  res_num_in_passive:                     0
% 1.86/0.98  res_num_in_active:                      0
% 1.86/0.98  res_num_of_loops:                       119
% 1.86/0.98  res_forward_subset_subsumed:            33
% 1.86/0.98  res_backward_subset_subsumed:           0
% 1.86/0.98  res_forward_subsumed:                   0
% 1.86/0.98  res_backward_subsumed:                  0
% 1.86/0.98  res_forward_subsumption_resolution:     0
% 1.86/0.98  res_backward_subsumption_resolution:    0
% 1.86/0.98  res_clause_to_clause_subsumption:       112
% 1.86/0.98  res_orphan_elimination:                 0
% 1.86/0.98  res_tautology_del:                      29
% 1.86/0.98  res_num_eq_res_simplified:              0
% 1.86/0.98  res_num_sel_changes:                    0
% 1.86/0.98  res_moves_from_active_to_pass:          0
% 1.86/0.98  
% 1.86/0.98  ------ Superposition
% 1.86/0.98  
% 1.86/0.98  sup_time_total:                         0.
% 1.86/0.98  sup_time_generating:                    0.
% 1.86/0.98  sup_time_sim_full:                      0.
% 1.86/0.98  sup_time_sim_immed:                     0.
% 1.86/0.98  
% 1.86/0.98  sup_num_of_clauses:                     48
% 1.86/0.98  sup_num_in_active:                      39
% 1.86/0.98  sup_num_in_passive:                     9
% 1.86/0.98  sup_num_of_loops:                       42
% 1.86/0.98  sup_fw_superposition:                   13
% 1.86/0.98  sup_bw_superposition:                   14
% 1.86/0.98  sup_immediate_simplified:               4
% 1.86/0.98  sup_given_eliminated:                   0
% 1.86/0.98  comparisons_done:                       0
% 1.86/0.98  comparisons_avoided:                    0
% 1.86/0.98  
% 1.86/0.98  ------ Simplifications
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  sim_fw_subset_subsumed:                 1
% 1.86/0.98  sim_bw_subset_subsumed:                 0
% 1.86/0.98  sim_fw_subsumed:                        0
% 1.86/0.98  sim_bw_subsumed:                        0
% 1.86/0.98  sim_fw_subsumption_res:                 1
% 1.86/0.98  sim_bw_subsumption_res:                 0
% 1.86/0.98  sim_tautology_del:                      0
% 1.86/0.98  sim_eq_tautology_del:                   0
% 1.86/0.98  sim_eq_res_simp:                        0
% 1.86/0.98  sim_fw_demodulated:                     2
% 1.86/0.98  sim_bw_demodulated:                     3
% 1.86/0.98  sim_light_normalised:                   3
% 1.86/0.98  sim_joinable_taut:                      0
% 1.86/0.98  sim_joinable_simp:                      0
% 1.86/0.98  sim_ac_normalised:                      0
% 1.86/0.98  sim_smt_subsumption:                    0
% 1.86/0.98  
%------------------------------------------------------------------------------
