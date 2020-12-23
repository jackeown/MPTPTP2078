%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:56 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 533 expanded)
%              Number of clauses        :   86 ( 128 expanded)
%              Number of leaves         :   14 ( 227 expanded)
%              Depth                    :   21
%              Number of atoms          :  632 (6939 expanded)
%              Number of equality atoms :  206 ( 742 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & r1_tarski(X5,u1_struct_0(X2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & r1_tarski(sK5,u1_struct_0(X2))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,
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

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f26,f25,f24,f23,f22,f21])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_450,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_922,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_452,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_920,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_455,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_917,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f33])).

cnf(c_462,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X3_53)
    | v2_struct_0(X1_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_911,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_2295,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_911])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_910,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1704,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k7_relat_1(sK4,X0_51)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_910])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_1882,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1704,c_15,c_13,c_1178])).

cnf(c_2349,plain,
    ( k3_tmap_1(X0_53,sK1,sK3,X1_53,sK4) = k7_relat_1(sK4,u1_struct_0(X1_53))
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2295,c_1882])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_29,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_30,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_31,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_37,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2904,plain,
    ( v2_pre_topc(X0_53) != iProver_top
    | k3_tmap_1(X0_53,sK1,sK3,X1_53,sK4) = k7_relat_1(sK4,u1_struct_0(X1_53))
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2349,c_29,c_30,c_31,c_36,c_37])).

cnf(c_2905,plain,
    ( k3_tmap_1(X0_53,sK1,sK3,X1_53,sK4) = k7_relat_1(sK4,u1_struct_0(X1_53))
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | m1_pre_topc(X1_53,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2904])).

cnf(c_2917,plain,
    ( k3_tmap_1(sK0,sK1,sK3,X0_53,sK4) = k7_relat_1(sK4,u1_struct_0(X0_53))
    | m1_pre_topc(X0_53,sK0) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_2905])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_26,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_27,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2991,plain,
    ( m1_pre_topc(X0_53,sK3) != iProver_top
    | m1_pre_topc(X0_53,sK0) != iProver_top
    | k3_tmap_1(sK0,sK1,sK3,X0_53,sK4) = k7_relat_1(sK4,u1_struct_0(X0_53)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2917,c_26,c_27,c_28])).

cnf(c_2992,plain,
    ( k3_tmap_1(sK0,sK1,sK3,X0_53,sK4) = k7_relat_1(sK4,u1_struct_0(X0_53))
    | m1_pre_topc(X0_53,sK0) != iProver_top
    | m1_pre_topc(X0_53,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2991])).

cnf(c_3001,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_2992])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3130,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3001,c_39])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f36])).

cnf(c_461,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | m1_subset_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X3_53)
    | v2_struct_0(X1_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_912,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k7_relset_1(X1_51,X2_51,X0_51,X3_51) = k9_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_909,plain,
    ( k7_relset_1(X0_51,X1_51,X2_51,X3_51) = k9_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_1950,plain,
    ( k7_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),k3_tmap_1(X2_53,X1_53,X3_53,X0_53,X0_51),X1_51) = k9_relat_1(k3_tmap_1(X2_53,X1_53,X3_53,X0_53,X0_51),X1_51)
    | v1_funct_2(X0_51,u1_struct_0(X3_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_pre_topc(X3_53,X2_53) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_909])).

cnf(c_2381,plain,
    ( k7_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51) = k9_relat_1(k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_1950])).

cnf(c_2515,plain,
    ( v2_pre_topc(X1_53) != iProver_top
    | k7_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51) = k9_relat_1(k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2381,c_29,c_30,c_31,c_36,c_37])).

cnf(c_2516,plain,
    ( k7_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51) = k9_relat_1(k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(sK3,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2515])).

cnf(c_2529,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_51) = k9_relat_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_51)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_2516])).

cnf(c_35,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2665,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_51) = k9_relat_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2529,c_26,c_27,c_28,c_35])).

cnf(c_1698,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k9_relat_1(sK4,X0_51) ),
    inference(superposition,[status(thm)],[c_917,c_909])).

cnf(c_9,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_458,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1826,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_1698,c_458])).

cnf(c_2669,plain,
    ( k9_relat_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_2665,c_1826])).

cnf(c_3134,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3130,c_2669])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_907,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_1506,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_907])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1147,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X1_51,X2_51)) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_1315,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_1316,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1315])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_465,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1333,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_1334,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_1607,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1506,c_38,c_1316,c_1334])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_262,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | u1_struct_0(sK2) != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_263,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_442,plain,
    ( ~ v1_relat_1(X0_51)
    | k9_relat_1(k7_relat_1(X0_51,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_51,sK5) ),
    inference(subtyping,[status(esa)],[c_263])).

cnf(c_930,plain,
    ( k9_relat_1(k7_relat_1(X0_51,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_51,sK5)
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_1615,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1607,c_930])).

cnf(c_3139,plain,
    ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3134,c_1615])).

cnf(c_3140,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3139])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.11/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/1.00  
% 2.11/1.00  ------  iProver source info
% 2.11/1.00  
% 2.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/1.00  git: non_committed_changes: false
% 2.11/1.00  git: last_make_outside_of_git: false
% 2.11/1.00  
% 2.11/1.00  ------ 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options
% 2.11/1.00  
% 2.11/1.00  --out_options                           all
% 2.11/1.00  --tptp_safe_out                         true
% 2.11/1.00  --problem_path                          ""
% 2.11/1.00  --include_path                          ""
% 2.11/1.00  --clausifier                            res/vclausify_rel
% 2.11/1.00  --clausifier_options                    --mode clausify
% 2.11/1.00  --stdin                                 false
% 2.11/1.00  --stats_out                             all
% 2.11/1.00  
% 2.11/1.00  ------ General Options
% 2.11/1.00  
% 2.11/1.00  --fof                                   false
% 2.11/1.00  --time_out_real                         305.
% 2.11/1.00  --time_out_virtual                      -1.
% 2.11/1.00  --symbol_type_check                     false
% 2.11/1.00  --clausify_out                          false
% 2.11/1.00  --sig_cnt_out                           false
% 2.11/1.00  --trig_cnt_out                          false
% 2.11/1.00  --trig_cnt_out_tolerance                1.
% 2.11/1.00  --trig_cnt_out_sk_spl                   false
% 2.11/1.00  --abstr_cl_out                          false
% 2.11/1.00  
% 2.11/1.00  ------ Global Options
% 2.11/1.00  
% 2.11/1.00  --schedule                              default
% 2.11/1.00  --add_important_lit                     false
% 2.11/1.00  --prop_solver_per_cl                    1000
% 2.11/1.00  --min_unsat_core                        false
% 2.11/1.00  --soft_assumptions                      false
% 2.11/1.00  --soft_lemma_size                       3
% 2.11/1.00  --prop_impl_unit_size                   0
% 2.11/1.00  --prop_impl_unit                        []
% 2.11/1.00  --share_sel_clauses                     true
% 2.11/1.00  --reset_solvers                         false
% 2.11/1.00  --bc_imp_inh                            [conj_cone]
% 2.11/1.00  --conj_cone_tolerance                   3.
% 2.11/1.00  --extra_neg_conj                        none
% 2.11/1.00  --large_theory_mode                     true
% 2.11/1.00  --prolific_symb_bound                   200
% 2.11/1.00  --lt_threshold                          2000
% 2.11/1.00  --clause_weak_htbl                      true
% 2.11/1.00  --gc_record_bc_elim                     false
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing Options
% 2.11/1.00  
% 2.11/1.00  --preprocessing_flag                    true
% 2.11/1.00  --time_out_prep_mult                    0.1
% 2.11/1.00  --splitting_mode                        input
% 2.11/1.00  --splitting_grd                         true
% 2.11/1.00  --splitting_cvd                         false
% 2.11/1.00  --splitting_cvd_svl                     false
% 2.11/1.00  --splitting_nvd                         32
% 2.11/1.00  --sub_typing                            true
% 2.11/1.00  --prep_gs_sim                           true
% 2.11/1.00  --prep_unflatten                        true
% 2.11/1.00  --prep_res_sim                          true
% 2.11/1.00  --prep_upred                            true
% 2.11/1.00  --prep_sem_filter                       exhaustive
% 2.11/1.00  --prep_sem_filter_out                   false
% 2.11/1.00  --pred_elim                             true
% 2.11/1.00  --res_sim_input                         true
% 2.11/1.00  --eq_ax_congr_red                       true
% 2.11/1.00  --pure_diseq_elim                       true
% 2.11/1.00  --brand_transform                       false
% 2.11/1.00  --non_eq_to_eq                          false
% 2.11/1.00  --prep_def_merge                        true
% 2.11/1.00  --prep_def_merge_prop_impl              false
% 2.11/1.00  --prep_def_merge_mbd                    true
% 2.11/1.00  --prep_def_merge_tr_red                 false
% 2.11/1.00  --prep_def_merge_tr_cl                  false
% 2.11/1.00  --smt_preprocessing                     true
% 2.11/1.00  --smt_ac_axioms                         fast
% 2.11/1.00  --preprocessed_out                      false
% 2.11/1.00  --preprocessed_stats                    false
% 2.11/1.00  
% 2.11/1.00  ------ Abstraction refinement Options
% 2.11/1.00  
% 2.11/1.00  --abstr_ref                             []
% 2.11/1.00  --abstr_ref_prep                        false
% 2.11/1.00  --abstr_ref_until_sat                   false
% 2.11/1.00  --abstr_ref_sig_restrict                funpre
% 2.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.00  --abstr_ref_under                       []
% 2.11/1.00  
% 2.11/1.00  ------ SAT Options
% 2.11/1.00  
% 2.11/1.00  --sat_mode                              false
% 2.11/1.00  --sat_fm_restart_options                ""
% 2.11/1.00  --sat_gr_def                            false
% 2.11/1.00  --sat_epr_types                         true
% 2.11/1.00  --sat_non_cyclic_types                  false
% 2.11/1.00  --sat_finite_models                     false
% 2.11/1.00  --sat_fm_lemmas                         false
% 2.11/1.00  --sat_fm_prep                           false
% 2.11/1.00  --sat_fm_uc_incr                        true
% 2.11/1.00  --sat_out_model                         small
% 2.11/1.00  --sat_out_clauses                       false
% 2.11/1.00  
% 2.11/1.00  ------ QBF Options
% 2.11/1.00  
% 2.11/1.00  --qbf_mode                              false
% 2.11/1.00  --qbf_elim_univ                         false
% 2.11/1.00  --qbf_dom_inst                          none
% 2.11/1.00  --qbf_dom_pre_inst                      false
% 2.11/1.00  --qbf_sk_in                             false
% 2.11/1.00  --qbf_pred_elim                         true
% 2.11/1.00  --qbf_split                             512
% 2.11/1.00  
% 2.11/1.00  ------ BMC1 Options
% 2.11/1.00  
% 2.11/1.00  --bmc1_incremental                      false
% 2.11/1.00  --bmc1_axioms                           reachable_all
% 2.11/1.00  --bmc1_min_bound                        0
% 2.11/1.00  --bmc1_max_bound                        -1
% 2.11/1.00  --bmc1_max_bound_default                -1
% 2.11/1.00  --bmc1_symbol_reachability              true
% 2.11/1.00  --bmc1_property_lemmas                  false
% 2.11/1.00  --bmc1_k_induction                      false
% 2.11/1.00  --bmc1_non_equiv_states                 false
% 2.11/1.00  --bmc1_deadlock                         false
% 2.11/1.00  --bmc1_ucm                              false
% 2.11/1.00  --bmc1_add_unsat_core                   none
% 2.11/1.00  --bmc1_unsat_core_children              false
% 2.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.00  --bmc1_out_stat                         full
% 2.11/1.00  --bmc1_ground_init                      false
% 2.11/1.00  --bmc1_pre_inst_next_state              false
% 2.11/1.00  --bmc1_pre_inst_state                   false
% 2.11/1.00  --bmc1_pre_inst_reach_state             false
% 2.11/1.00  --bmc1_out_unsat_core                   false
% 2.11/1.00  --bmc1_aig_witness_out                  false
% 2.11/1.00  --bmc1_verbose                          false
% 2.11/1.00  --bmc1_dump_clauses_tptp                false
% 2.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.00  --bmc1_dump_file                        -
% 2.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.00  --bmc1_ucm_extend_mode                  1
% 2.11/1.00  --bmc1_ucm_init_mode                    2
% 2.11/1.00  --bmc1_ucm_cone_mode                    none
% 2.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.00  --bmc1_ucm_relax_model                  4
% 2.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.00  --bmc1_ucm_layered_model                none
% 2.11/1.00  --bmc1_ucm_max_lemma_size               10
% 2.11/1.00  
% 2.11/1.00  ------ AIG Options
% 2.11/1.00  
% 2.11/1.00  --aig_mode                              false
% 2.11/1.00  
% 2.11/1.00  ------ Instantiation Options
% 2.11/1.00  
% 2.11/1.00  --instantiation_flag                    true
% 2.11/1.00  --inst_sos_flag                         false
% 2.11/1.00  --inst_sos_phase                        true
% 2.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel_side                     num_symb
% 2.11/1.00  --inst_solver_per_active                1400
% 2.11/1.00  --inst_solver_calls_frac                1.
% 2.11/1.00  --inst_passive_queue_type               priority_queues
% 2.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.00  --inst_passive_queues_freq              [25;2]
% 2.11/1.00  --inst_dismatching                      true
% 2.11/1.00  --inst_eager_unprocessed_to_passive     true
% 2.11/1.00  --inst_prop_sim_given                   true
% 2.11/1.00  --inst_prop_sim_new                     false
% 2.11/1.00  --inst_subs_new                         false
% 2.11/1.00  --inst_eq_res_simp                      false
% 2.11/1.00  --inst_subs_given                       false
% 2.11/1.00  --inst_orphan_elimination               true
% 2.11/1.00  --inst_learning_loop_flag               true
% 2.11/1.00  --inst_learning_start                   3000
% 2.11/1.00  --inst_learning_factor                  2
% 2.11/1.00  --inst_start_prop_sim_after_learn       3
% 2.11/1.00  --inst_sel_renew                        solver
% 2.11/1.00  --inst_lit_activity_flag                true
% 2.11/1.00  --inst_restr_to_given                   false
% 2.11/1.00  --inst_activity_threshold               500
% 2.11/1.00  --inst_out_proof                        true
% 2.11/1.00  
% 2.11/1.00  ------ Resolution Options
% 2.11/1.00  
% 2.11/1.00  --resolution_flag                       true
% 2.11/1.00  --res_lit_sel                           adaptive
% 2.11/1.00  --res_lit_sel_side                      none
% 2.11/1.00  --res_ordering                          kbo
% 2.11/1.00  --res_to_prop_solver                    active
% 2.11/1.00  --res_prop_simpl_new                    false
% 2.11/1.00  --res_prop_simpl_given                  true
% 2.11/1.00  --res_passive_queue_type                priority_queues
% 2.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.00  --res_passive_queues_freq               [15;5]
% 2.11/1.00  --res_forward_subs                      full
% 2.11/1.00  --res_backward_subs                     full
% 2.11/1.00  --res_forward_subs_resolution           true
% 2.11/1.00  --res_backward_subs_resolution          true
% 2.11/1.00  --res_orphan_elimination                true
% 2.11/1.00  --res_time_limit                        2.
% 2.11/1.00  --res_out_proof                         true
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Options
% 2.11/1.00  
% 2.11/1.00  --superposition_flag                    true
% 2.11/1.00  --sup_passive_queue_type                priority_queues
% 2.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.00  --demod_completeness_check              fast
% 2.11/1.00  --demod_use_ground                      true
% 2.11/1.00  --sup_to_prop_solver                    passive
% 2.11/1.00  --sup_prop_simpl_new                    true
% 2.11/1.00  --sup_prop_simpl_given                  true
% 2.11/1.00  --sup_fun_splitting                     false
% 2.11/1.00  --sup_smt_interval                      50000
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Simplification Setup
% 2.11/1.00  
% 2.11/1.00  --sup_indices_passive                   []
% 2.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_full_bw                           [BwDemod]
% 2.11/1.00  --sup_immed_triv                        [TrivRules]
% 2.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_immed_bw_main                     []
% 2.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  
% 2.11/1.00  ------ Combination Options
% 2.11/1.00  
% 2.11/1.00  --comb_res_mult                         3
% 2.11/1.00  --comb_sup_mult                         2
% 2.11/1.00  --comb_inst_mult                        10
% 2.11/1.00  
% 2.11/1.00  ------ Debug Options
% 2.11/1.00  
% 2.11/1.00  --dbg_backtrace                         false
% 2.11/1.00  --dbg_dump_prop_clauses                 false
% 2.11/1.00  --dbg_dump_prop_clauses_file            -
% 2.11/1.00  --dbg_out_stat                          false
% 2.11/1.00  ------ Parsing...
% 2.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.11/1.00  ------ Proving...
% 2.11/1.00  ------ Problem Properties 
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  clauses                                 25
% 2.11/1.00  conjectures                             16
% 2.11/1.00  EPR                                     12
% 2.11/1.00  Horn                                    21
% 2.11/1.00  unary                                   17
% 2.11/1.00  binary                                  2
% 2.11/1.00  lits                                    76
% 2.11/1.00  lits eq                                 5
% 2.11/1.00  fd_pure                                 0
% 2.11/1.00  fd_pseudo                               0
% 2.11/1.00  fd_cond                                 0
% 2.11/1.00  fd_pseudo_cond                          0
% 2.11/1.00  AC symbols                              0
% 2.11/1.00  
% 2.11/1.00  ------ Schedule dynamic 5 is on 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  ------ 
% 2.11/1.00  Current options:
% 2.11/1.00  ------ 
% 2.11/1.00  
% 2.11/1.00  ------ Input Options
% 2.11/1.00  
% 2.11/1.00  --out_options                           all
% 2.11/1.00  --tptp_safe_out                         true
% 2.11/1.00  --problem_path                          ""
% 2.11/1.00  --include_path                          ""
% 2.11/1.00  --clausifier                            res/vclausify_rel
% 2.11/1.00  --clausifier_options                    --mode clausify
% 2.11/1.00  --stdin                                 false
% 2.11/1.00  --stats_out                             all
% 2.11/1.00  
% 2.11/1.00  ------ General Options
% 2.11/1.00  
% 2.11/1.00  --fof                                   false
% 2.11/1.00  --time_out_real                         305.
% 2.11/1.00  --time_out_virtual                      -1.
% 2.11/1.00  --symbol_type_check                     false
% 2.11/1.00  --clausify_out                          false
% 2.11/1.00  --sig_cnt_out                           false
% 2.11/1.00  --trig_cnt_out                          false
% 2.11/1.00  --trig_cnt_out_tolerance                1.
% 2.11/1.00  --trig_cnt_out_sk_spl                   false
% 2.11/1.00  --abstr_cl_out                          false
% 2.11/1.00  
% 2.11/1.00  ------ Global Options
% 2.11/1.00  
% 2.11/1.00  --schedule                              default
% 2.11/1.00  --add_important_lit                     false
% 2.11/1.00  --prop_solver_per_cl                    1000
% 2.11/1.00  --min_unsat_core                        false
% 2.11/1.00  --soft_assumptions                      false
% 2.11/1.00  --soft_lemma_size                       3
% 2.11/1.00  --prop_impl_unit_size                   0
% 2.11/1.00  --prop_impl_unit                        []
% 2.11/1.00  --share_sel_clauses                     true
% 2.11/1.00  --reset_solvers                         false
% 2.11/1.00  --bc_imp_inh                            [conj_cone]
% 2.11/1.00  --conj_cone_tolerance                   3.
% 2.11/1.00  --extra_neg_conj                        none
% 2.11/1.00  --large_theory_mode                     true
% 2.11/1.00  --prolific_symb_bound                   200
% 2.11/1.00  --lt_threshold                          2000
% 2.11/1.00  --clause_weak_htbl                      true
% 2.11/1.00  --gc_record_bc_elim                     false
% 2.11/1.00  
% 2.11/1.00  ------ Preprocessing Options
% 2.11/1.00  
% 2.11/1.00  --preprocessing_flag                    true
% 2.11/1.00  --time_out_prep_mult                    0.1
% 2.11/1.00  --splitting_mode                        input
% 2.11/1.00  --splitting_grd                         true
% 2.11/1.00  --splitting_cvd                         false
% 2.11/1.00  --splitting_cvd_svl                     false
% 2.11/1.00  --splitting_nvd                         32
% 2.11/1.00  --sub_typing                            true
% 2.11/1.00  --prep_gs_sim                           true
% 2.11/1.00  --prep_unflatten                        true
% 2.11/1.00  --prep_res_sim                          true
% 2.11/1.00  --prep_upred                            true
% 2.11/1.00  --prep_sem_filter                       exhaustive
% 2.11/1.00  --prep_sem_filter_out                   false
% 2.11/1.00  --pred_elim                             true
% 2.11/1.00  --res_sim_input                         true
% 2.11/1.00  --eq_ax_congr_red                       true
% 2.11/1.00  --pure_diseq_elim                       true
% 2.11/1.00  --brand_transform                       false
% 2.11/1.00  --non_eq_to_eq                          false
% 2.11/1.00  --prep_def_merge                        true
% 2.11/1.00  --prep_def_merge_prop_impl              false
% 2.11/1.00  --prep_def_merge_mbd                    true
% 2.11/1.00  --prep_def_merge_tr_red                 false
% 2.11/1.00  --prep_def_merge_tr_cl                  false
% 2.11/1.00  --smt_preprocessing                     true
% 2.11/1.00  --smt_ac_axioms                         fast
% 2.11/1.00  --preprocessed_out                      false
% 2.11/1.00  --preprocessed_stats                    false
% 2.11/1.00  
% 2.11/1.00  ------ Abstraction refinement Options
% 2.11/1.00  
% 2.11/1.00  --abstr_ref                             []
% 2.11/1.00  --abstr_ref_prep                        false
% 2.11/1.00  --abstr_ref_until_sat                   false
% 2.11/1.00  --abstr_ref_sig_restrict                funpre
% 2.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/1.00  --abstr_ref_under                       []
% 2.11/1.00  
% 2.11/1.00  ------ SAT Options
% 2.11/1.00  
% 2.11/1.00  --sat_mode                              false
% 2.11/1.00  --sat_fm_restart_options                ""
% 2.11/1.00  --sat_gr_def                            false
% 2.11/1.00  --sat_epr_types                         true
% 2.11/1.00  --sat_non_cyclic_types                  false
% 2.11/1.00  --sat_finite_models                     false
% 2.11/1.00  --sat_fm_lemmas                         false
% 2.11/1.00  --sat_fm_prep                           false
% 2.11/1.00  --sat_fm_uc_incr                        true
% 2.11/1.00  --sat_out_model                         small
% 2.11/1.00  --sat_out_clauses                       false
% 2.11/1.00  
% 2.11/1.00  ------ QBF Options
% 2.11/1.00  
% 2.11/1.00  --qbf_mode                              false
% 2.11/1.00  --qbf_elim_univ                         false
% 2.11/1.00  --qbf_dom_inst                          none
% 2.11/1.00  --qbf_dom_pre_inst                      false
% 2.11/1.00  --qbf_sk_in                             false
% 2.11/1.00  --qbf_pred_elim                         true
% 2.11/1.00  --qbf_split                             512
% 2.11/1.00  
% 2.11/1.00  ------ BMC1 Options
% 2.11/1.00  
% 2.11/1.00  --bmc1_incremental                      false
% 2.11/1.00  --bmc1_axioms                           reachable_all
% 2.11/1.00  --bmc1_min_bound                        0
% 2.11/1.00  --bmc1_max_bound                        -1
% 2.11/1.00  --bmc1_max_bound_default                -1
% 2.11/1.00  --bmc1_symbol_reachability              true
% 2.11/1.00  --bmc1_property_lemmas                  false
% 2.11/1.00  --bmc1_k_induction                      false
% 2.11/1.00  --bmc1_non_equiv_states                 false
% 2.11/1.00  --bmc1_deadlock                         false
% 2.11/1.00  --bmc1_ucm                              false
% 2.11/1.00  --bmc1_add_unsat_core                   none
% 2.11/1.00  --bmc1_unsat_core_children              false
% 2.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/1.00  --bmc1_out_stat                         full
% 2.11/1.00  --bmc1_ground_init                      false
% 2.11/1.00  --bmc1_pre_inst_next_state              false
% 2.11/1.00  --bmc1_pre_inst_state                   false
% 2.11/1.00  --bmc1_pre_inst_reach_state             false
% 2.11/1.00  --bmc1_out_unsat_core                   false
% 2.11/1.00  --bmc1_aig_witness_out                  false
% 2.11/1.00  --bmc1_verbose                          false
% 2.11/1.00  --bmc1_dump_clauses_tptp                false
% 2.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.11/1.00  --bmc1_dump_file                        -
% 2.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.11/1.00  --bmc1_ucm_extend_mode                  1
% 2.11/1.00  --bmc1_ucm_init_mode                    2
% 2.11/1.00  --bmc1_ucm_cone_mode                    none
% 2.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.11/1.00  --bmc1_ucm_relax_model                  4
% 2.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/1.00  --bmc1_ucm_layered_model                none
% 2.11/1.00  --bmc1_ucm_max_lemma_size               10
% 2.11/1.00  
% 2.11/1.00  ------ AIG Options
% 2.11/1.00  
% 2.11/1.00  --aig_mode                              false
% 2.11/1.00  
% 2.11/1.00  ------ Instantiation Options
% 2.11/1.00  
% 2.11/1.00  --instantiation_flag                    true
% 2.11/1.00  --inst_sos_flag                         false
% 2.11/1.00  --inst_sos_phase                        true
% 2.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/1.00  --inst_lit_sel_side                     none
% 2.11/1.00  --inst_solver_per_active                1400
% 2.11/1.00  --inst_solver_calls_frac                1.
% 2.11/1.00  --inst_passive_queue_type               priority_queues
% 2.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/1.00  --inst_passive_queues_freq              [25;2]
% 2.11/1.00  --inst_dismatching                      true
% 2.11/1.00  --inst_eager_unprocessed_to_passive     true
% 2.11/1.00  --inst_prop_sim_given                   true
% 2.11/1.00  --inst_prop_sim_new                     false
% 2.11/1.00  --inst_subs_new                         false
% 2.11/1.00  --inst_eq_res_simp                      false
% 2.11/1.00  --inst_subs_given                       false
% 2.11/1.00  --inst_orphan_elimination               true
% 2.11/1.00  --inst_learning_loop_flag               true
% 2.11/1.00  --inst_learning_start                   3000
% 2.11/1.00  --inst_learning_factor                  2
% 2.11/1.00  --inst_start_prop_sim_after_learn       3
% 2.11/1.00  --inst_sel_renew                        solver
% 2.11/1.00  --inst_lit_activity_flag                true
% 2.11/1.00  --inst_restr_to_given                   false
% 2.11/1.00  --inst_activity_threshold               500
% 2.11/1.00  --inst_out_proof                        true
% 2.11/1.00  
% 2.11/1.00  ------ Resolution Options
% 2.11/1.00  
% 2.11/1.00  --resolution_flag                       false
% 2.11/1.00  --res_lit_sel                           adaptive
% 2.11/1.00  --res_lit_sel_side                      none
% 2.11/1.00  --res_ordering                          kbo
% 2.11/1.00  --res_to_prop_solver                    active
% 2.11/1.00  --res_prop_simpl_new                    false
% 2.11/1.00  --res_prop_simpl_given                  true
% 2.11/1.00  --res_passive_queue_type                priority_queues
% 2.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/1.00  --res_passive_queues_freq               [15;5]
% 2.11/1.00  --res_forward_subs                      full
% 2.11/1.00  --res_backward_subs                     full
% 2.11/1.00  --res_forward_subs_resolution           true
% 2.11/1.00  --res_backward_subs_resolution          true
% 2.11/1.00  --res_orphan_elimination                true
% 2.11/1.00  --res_time_limit                        2.
% 2.11/1.00  --res_out_proof                         true
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Options
% 2.11/1.00  
% 2.11/1.00  --superposition_flag                    true
% 2.11/1.00  --sup_passive_queue_type                priority_queues
% 2.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.11/1.00  --demod_completeness_check              fast
% 2.11/1.00  --demod_use_ground                      true
% 2.11/1.00  --sup_to_prop_solver                    passive
% 2.11/1.00  --sup_prop_simpl_new                    true
% 2.11/1.00  --sup_prop_simpl_given                  true
% 2.11/1.00  --sup_fun_splitting                     false
% 2.11/1.00  --sup_smt_interval                      50000
% 2.11/1.00  
% 2.11/1.00  ------ Superposition Simplification Setup
% 2.11/1.00  
% 2.11/1.00  --sup_indices_passive                   []
% 2.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_full_bw                           [BwDemod]
% 2.11/1.00  --sup_immed_triv                        [TrivRules]
% 2.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_immed_bw_main                     []
% 2.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/1.00  
% 2.11/1.00  ------ Combination Options
% 2.11/1.00  
% 2.11/1.00  --comb_res_mult                         3
% 2.11/1.00  --comb_sup_mult                         2
% 2.11/1.00  --comb_inst_mult                        10
% 2.11/1.00  
% 2.11/1.00  ------ Debug Options
% 2.11/1.00  
% 2.11/1.00  --dbg_backtrace                         false
% 2.11/1.00  --dbg_dump_prop_clauses                 false
% 2.11/1.00  --dbg_dump_prop_clauses_file            -
% 2.11/1.00  --dbg_out_stat                          false
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  ------ Proving...
% 2.11/1.00  
% 2.11/1.00  
% 2.11/1.00  % SZS status Theorem for theBenchmark.p
% 2.11/1.00  
% 2.11/1.00   Resolution empty clause
% 2.11/1.00  
% 2.11/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/1.00  
% 2.11/1.00  fof(f8,conjecture,(
% 2.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f9,negated_conjecture,(
% 2.11/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.11/1.00    inference(negated_conjecture,[],[f8])).
% 2.11/1.00  
% 2.11/1.00  fof(f19,plain,(
% 2.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.11/1.00    inference(ennf_transformation,[],[f9])).
% 2.11/1.00  
% 2.11/1.00  fof(f20,plain,(
% 2.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.11/1.00    inference(flattening,[],[f19])).
% 2.11/1.00  
% 2.11/1.00  fof(f26,plain,(
% 2.11/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5) & r1_tarski(sK5,u1_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.11/1.00    introduced(choice_axiom,[])).
% 2.11/1.00  
% 2.11/1.00  fof(f25,plain,(
% 2.11/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.11/1.00    introduced(choice_axiom,[])).
% 2.11/1.00  
% 2.11/1.00  fof(f24,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.11/1.00    introduced(choice_axiom,[])).
% 2.11/1.00  
% 2.11/1.00  fof(f23,plain,(
% 2.11/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.11/1.00    introduced(choice_axiom,[])).
% 2.11/1.00  
% 2.11/1.00  fof(f22,plain,(
% 2.11/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.11/1.00    introduced(choice_axiom,[])).
% 2.11/1.00  
% 2.11/1.00  fof(f21,plain,(
% 2.11/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.11/1.00    introduced(choice_axiom,[])).
% 2.11/1.00  
% 2.11/1.00  fof(f27,plain,(
% 2.11/1.00    (((((k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.11/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f26,f25,f24,f23,f22,f21])).
% 2.11/1.00  
% 2.11/1.00  fof(f44,plain,(
% 2.11/1.00    m1_pre_topc(sK2,sK0)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f46,plain,(
% 2.11/1.00    m1_pre_topc(sK3,sK0)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f49,plain,(
% 2.11/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f6,axiom,(
% 2.11/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f15,plain,(
% 2.11/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.11/1.00    inference(ennf_transformation,[],[f6])).
% 2.11/1.00  
% 2.11/1.00  fof(f16,plain,(
% 2.11/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.11/1.00    inference(flattening,[],[f15])).
% 2.11/1.00  
% 2.11/1.00  fof(f33,plain,(
% 2.11/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f16])).
% 2.11/1.00  
% 2.11/1.00  fof(f5,axiom,(
% 2.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f13,plain,(
% 2.11/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.11/1.00    inference(ennf_transformation,[],[f5])).
% 2.11/1.00  
% 2.11/1.00  fof(f14,plain,(
% 2.11/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.11/1.00    inference(flattening,[],[f13])).
% 2.11/1.00  
% 2.11/1.00  fof(f32,plain,(
% 2.11/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f14])).
% 2.11/1.00  
% 2.11/1.00  fof(f47,plain,(
% 2.11/1.00    v1_funct_1(sK4)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f40,plain,(
% 2.11/1.00    ~v2_struct_0(sK1)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f41,plain,(
% 2.11/1.00    v2_pre_topc(sK1)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f42,plain,(
% 2.11/1.00    l1_pre_topc(sK1)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f48,plain,(
% 2.11/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f37,plain,(
% 2.11/1.00    ~v2_struct_0(sK0)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f38,plain,(
% 2.11/1.00    v2_pre_topc(sK0)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f39,plain,(
% 2.11/1.00    l1_pre_topc(sK0)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f50,plain,(
% 2.11/1.00    m1_pre_topc(sK2,sK3)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f7,axiom,(
% 2.11/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f17,plain,(
% 2.11/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.11/1.00    inference(ennf_transformation,[],[f7])).
% 2.11/1.00  
% 2.11/1.00  fof(f18,plain,(
% 2.11/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.11/1.00    inference(flattening,[],[f17])).
% 2.11/1.00  
% 2.11/1.00  fof(f36,plain,(
% 2.11/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f18])).
% 2.11/1.00  
% 2.11/1.00  fof(f4,axiom,(
% 2.11/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f12,plain,(
% 2.11/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/1.00    inference(ennf_transformation,[],[f4])).
% 2.11/1.00  
% 2.11/1.00  fof(f31,plain,(
% 2.11/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f12])).
% 2.11/1.00  
% 2.11/1.00  fof(f53,plain,(
% 2.11/1.00    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  fof(f1,axiom,(
% 2.11/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f10,plain,(
% 2.11/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.11/1.00    inference(ennf_transformation,[],[f1])).
% 2.11/1.00  
% 2.11/1.00  fof(f28,plain,(
% 2.11/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f10])).
% 2.11/1.00  
% 2.11/1.00  fof(f2,axiom,(
% 2.11/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f29,plain,(
% 2.11/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.11/1.00    inference(cnf_transformation,[],[f2])).
% 2.11/1.00  
% 2.11/1.00  fof(f3,axiom,(
% 2.11/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 2.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.11/1.00  
% 2.11/1.00  fof(f11,plain,(
% 2.11/1.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.11/1.00    inference(ennf_transformation,[],[f3])).
% 2.11/1.00  
% 2.11/1.00  fof(f30,plain,(
% 2.11/1.00    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 2.11/1.00    inference(cnf_transformation,[],[f11])).
% 2.11/1.00  
% 2.11/1.00  fof(f52,plain,(
% 2.11/1.00    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.11/1.00    inference(cnf_transformation,[],[f27])).
% 2.11/1.00  
% 2.11/1.00  cnf(c_18,negated_conjecture,
% 2.11/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_450,negated_conjecture,
% 2.11/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.11/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_922,plain,
% 2.11/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_16,negated_conjecture,
% 2.11/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_452,negated_conjecture,
% 2.11/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.11/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_920,plain,
% 2.11/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_13,negated_conjecture,
% 2.11/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.11/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_455,negated_conjecture,
% 2.11/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.11/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_917,plain,
% 2.11/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_5,plain,
% 2.11/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.11/1.00      | ~ m1_pre_topc(X3,X1)
% 2.11/1.00      | ~ m1_pre_topc(X3,X4)
% 2.11/1.00      | ~ m1_pre_topc(X1,X4)
% 2.11/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.11/1.00      | v2_struct_0(X4)
% 2.11/1.00      | v2_struct_0(X2)
% 2.11/1.00      | ~ v2_pre_topc(X2)
% 2.11/1.00      | ~ v2_pre_topc(X4)
% 2.11/1.00      | ~ l1_pre_topc(X2)
% 2.11/1.00      | ~ l1_pre_topc(X4)
% 2.11/1.00      | ~ v1_funct_1(X0)
% 2.11/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_462,plain,
% 2.11/1.00      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.11/1.00      | ~ m1_pre_topc(X2_53,X3_53)
% 2.11/1.00      | ~ m1_pre_topc(X0_53,X3_53)
% 2.11/1.00      | ~ m1_pre_topc(X2_53,X0_53)
% 2.11/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.11/1.00      | v2_struct_0(X3_53)
% 2.11/1.00      | v2_struct_0(X1_53)
% 2.11/1.00      | ~ v2_pre_topc(X1_53)
% 2.11/1.00      | ~ v2_pre_topc(X3_53)
% 2.11/1.00      | ~ l1_pre_topc(X1_53)
% 2.11/1.00      | ~ l1_pre_topc(X3_53)
% 2.11/1.00      | ~ v1_funct_1(X0_51)
% 2.11/1.00      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_51) ),
% 2.11/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_911,plain,
% 2.11/1.00      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_51)
% 2.11/1.00      | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.11/1.00      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 2.11/1.00      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.11/1.00      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.11/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.11/1.00      | v2_struct_0(X3_53) = iProver_top
% 2.11/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.11/1.00      | v2_pre_topc(X3_53) != iProver_top
% 2.11/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.11/1.00      | l1_pre_topc(X3_53) != iProver_top
% 2.11/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.11/1.00      | v1_funct_1(X0_51) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2295,plain,
% 2.11/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4)
% 2.11/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.11/1.00      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.11/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.11/1.00      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.11/1.00      | v2_struct_0(X1_53) = iProver_top
% 2.11/1.00      | v2_struct_0(sK1) = iProver_top
% 2.11/1.00      | v2_pre_topc(X1_53) != iProver_top
% 2.11/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.11/1.00      | l1_pre_topc(X1_53) != iProver_top
% 2.11/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.11/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_917,c_911]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_4,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/1.00      | ~ v1_funct_1(X0)
% 2.11/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.11/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_463,plain,
% 2.11/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.11/1.00      | ~ v1_funct_1(X0_51)
% 2.11/1.00      | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
% 2.11/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_910,plain,
% 2.11/1.00      ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
% 2.11/1.00      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.11/1.00      | v1_funct_1(X2_51) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1704,plain,
% 2.11/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k7_relat_1(sK4,X0_51)
% 2.11/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_917,c_910]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_15,negated_conjecture,
% 2.11/1.00      ( v1_funct_1(sK4) ),
% 2.11/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1178,plain,
% 2.11/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.11/1.00      | ~ v1_funct_1(sK4)
% 2.11/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 2.11/1.00      inference(instantiation,[status(thm)],[c_463]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_1882,plain,
% 2.11/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 2.11/1.00      inference(global_propositional_subsumption,
% 2.11/1.00                [status(thm)],
% 2.11/1.00                [c_1704,c_15,c_13,c_1178]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2349,plain,
% 2.11/1.00      ( k3_tmap_1(X0_53,sK1,sK3,X1_53,sK4) = k7_relat_1(sK4,u1_struct_0(X1_53))
% 2.11/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.11/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.11/1.00      | m1_pre_topc(X1_53,sK3) != iProver_top
% 2.11/1.00      | m1_pre_topc(sK3,X0_53) != iProver_top
% 2.11/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.11/1.00      | v2_struct_0(sK1) = iProver_top
% 2.11/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.11/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.11/1.00      | l1_pre_topc(X0_53) != iProver_top
% 2.11/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.11/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.11/1.00      inference(demodulation,[status(thm)],[c_2295,c_1882]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_22,negated_conjecture,
% 2.11/1.00      ( ~ v2_struct_0(sK1) ),
% 2.11/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_29,plain,
% 2.11/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_21,negated_conjecture,
% 2.11/1.00      ( v2_pre_topc(sK1) ),
% 2.11/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_30,plain,
% 2.11/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_20,negated_conjecture,
% 2.11/1.00      ( l1_pre_topc(sK1) ),
% 2.11/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_31,plain,
% 2.11/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_36,plain,
% 2.11/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_14,negated_conjecture,
% 2.11/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.11/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_37,plain,
% 2.11/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2904,plain,
% 2.11/1.00      ( v2_pre_topc(X0_53) != iProver_top
% 2.11/1.00      | k3_tmap_1(X0_53,sK1,sK3,X1_53,sK4) = k7_relat_1(sK4,u1_struct_0(X1_53))
% 2.11/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.11/1.00      | m1_pre_topc(X1_53,sK3) != iProver_top
% 2.11/1.00      | m1_pre_topc(sK3,X0_53) != iProver_top
% 2.11/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.11/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 2.11/1.00      inference(global_propositional_subsumption,
% 2.11/1.00                [status(thm)],
% 2.11/1.00                [c_2349,c_29,c_30,c_31,c_36,c_37]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2905,plain,
% 2.11/1.00      ( k3_tmap_1(X0_53,sK1,sK3,X1_53,sK4) = k7_relat_1(sK4,u1_struct_0(X1_53))
% 2.11/1.00      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 2.11/1.00      | m1_pre_topc(X1_53,sK3) != iProver_top
% 2.11/1.00      | m1_pre_topc(sK3,X0_53) != iProver_top
% 2.11/1.00      | v2_struct_0(X0_53) = iProver_top
% 2.11/1.00      | v2_pre_topc(X0_53) != iProver_top
% 2.11/1.00      | l1_pre_topc(X0_53) != iProver_top ),
% 2.11/1.00      inference(renaming,[status(thm)],[c_2904]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_2917,plain,
% 2.11/1.00      ( k3_tmap_1(sK0,sK1,sK3,X0_53,sK4) = k7_relat_1(sK4,u1_struct_0(X0_53))
% 2.11/1.00      | m1_pre_topc(X0_53,sK0) != iProver_top
% 2.11/1.00      | m1_pre_topc(X0_53,sK3) != iProver_top
% 2.11/1.00      | v2_struct_0(sK0) = iProver_top
% 2.11/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.11/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.11/1.00      inference(superposition,[status(thm)],[c_920,c_2905]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_25,negated_conjecture,
% 2.11/1.00      ( ~ v2_struct_0(sK0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_26,plain,
% 2.11/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_24,negated_conjecture,
% 2.11/1.00      ( v2_pre_topc(sK0) ),
% 2.11/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.11/1.00  
% 2.11/1.00  cnf(c_27,plain,
% 2.11/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.11/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_23,negated_conjecture,
% 2.11/1.01      ( l1_pre_topc(sK0) ),
% 2.11/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_28,plain,
% 2.11/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2991,plain,
% 2.11/1.01      ( m1_pre_topc(X0_53,sK3) != iProver_top
% 2.11/1.01      | m1_pre_topc(X0_53,sK0) != iProver_top
% 2.11/1.01      | k3_tmap_1(sK0,sK1,sK3,X0_53,sK4) = k7_relat_1(sK4,u1_struct_0(X0_53)) ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_2917,c_26,c_27,c_28]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2992,plain,
% 2.11/1.01      ( k3_tmap_1(sK0,sK1,sK3,X0_53,sK4) = k7_relat_1(sK4,u1_struct_0(X0_53))
% 2.11/1.01      | m1_pre_topc(X0_53,sK0) != iProver_top
% 2.11/1.01      | m1_pre_topc(X0_53,sK3) != iProver_top ),
% 2.11/1.01      inference(renaming,[status(thm)],[c_2991]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3001,plain,
% 2.11/1.01      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 2.11/1.01      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_922,c_2992]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_12,negated_conjecture,
% 2.11/1.01      ( m1_pre_topc(sK2,sK3) ),
% 2.11/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_39,plain,
% 2.11/1.01      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3130,plain,
% 2.11/1.01      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 2.11/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3001,c_39]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_6,plain,
% 2.11/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.11/1.01      | ~ m1_pre_topc(X3,X4)
% 2.11/1.01      | ~ m1_pre_topc(X1,X4)
% 2.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.11/1.01      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 2.11/1.01      | v2_struct_0(X4)
% 2.11/1.01      | v2_struct_0(X2)
% 2.11/1.01      | ~ v2_pre_topc(X2)
% 2.11/1.01      | ~ v2_pre_topc(X4)
% 2.11/1.01      | ~ l1_pre_topc(X2)
% 2.11/1.01      | ~ l1_pre_topc(X4)
% 2.11/1.01      | ~ v1_funct_1(X0) ),
% 2.11/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_461,plain,
% 2.11/1.01      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.11/1.01      | ~ m1_pre_topc(X2_53,X3_53)
% 2.11/1.01      | ~ m1_pre_topc(X0_53,X3_53)
% 2.11/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.11/1.01      | m1_subset_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 2.11/1.01      | v2_struct_0(X3_53)
% 2.11/1.01      | v2_struct_0(X1_53)
% 2.11/1.01      | ~ v2_pre_topc(X1_53)
% 2.11/1.01      | ~ v2_pre_topc(X3_53)
% 2.11/1.01      | ~ l1_pre_topc(X1_53)
% 2.11/1.01      | ~ l1_pre_topc(X3_53)
% 2.11/1.01      | ~ v1_funct_1(X0_51) ),
% 2.11/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_912,plain,
% 2.11/1.01      ( v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.11/1.01      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 2.11/1.01      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.11/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.11/1.01      | m1_subset_1(k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
% 2.11/1.01      | v2_struct_0(X3_53) = iProver_top
% 2.11/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.11/1.01      | v2_pre_topc(X3_53) != iProver_top
% 2.11/1.01      | v2_pre_topc(X1_53) != iProver_top
% 2.11/1.01      | l1_pre_topc(X3_53) != iProver_top
% 2.11/1.01      | l1_pre_topc(X1_53) != iProver_top
% 2.11/1.01      | v1_funct_1(X0_51) != iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.11/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.11/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_464,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.11/1.01      | k7_relset_1(X1_51,X2_51,X0_51,X3_51) = k9_relat_1(X0_51,X3_51) ),
% 2.11/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_909,plain,
% 2.11/1.01      ( k7_relset_1(X0_51,X1_51,X2_51,X3_51) = k9_relat_1(X2_51,X3_51)
% 2.11/1.01      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1950,plain,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),k3_tmap_1(X2_53,X1_53,X3_53,X0_53,X0_51),X1_51) = k9_relat_1(k3_tmap_1(X2_53,X1_53,X3_53,X0_53,X0_51),X1_51)
% 2.11/1.01      | v1_funct_2(X0_51,u1_struct_0(X3_53),u1_struct_0(X1_53)) != iProver_top
% 2.11/1.01      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 2.11/1.01      | m1_pre_topc(X3_53,X2_53) != iProver_top
% 2.11/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_53),u1_struct_0(X1_53)))) != iProver_top
% 2.11/1.01      | v2_struct_0(X2_53) = iProver_top
% 2.11/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.11/1.01      | v2_pre_topc(X2_53) != iProver_top
% 2.11/1.01      | v2_pre_topc(X1_53) != iProver_top
% 2.11/1.01      | l1_pre_topc(X2_53) != iProver_top
% 2.11/1.01      | l1_pre_topc(X1_53) != iProver_top
% 2.11/1.01      | v1_funct_1(X0_51) != iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_912,c_909]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2381,plain,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51) = k9_relat_1(k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51)
% 2.11/1.01      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.11/1.01      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.11/1.01      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.11/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.11/1.01      | v2_struct_0(sK1) = iProver_top
% 2.11/1.01      | v2_pre_topc(X1_53) != iProver_top
% 2.11/1.01      | v2_pre_topc(sK1) != iProver_top
% 2.11/1.01      | l1_pre_topc(X1_53) != iProver_top
% 2.11/1.01      | l1_pre_topc(sK1) != iProver_top
% 2.11/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_917,c_1950]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2515,plain,
% 2.11/1.01      ( v2_pre_topc(X1_53) != iProver_top
% 2.11/1.01      | k7_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51) = k9_relat_1(k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51)
% 2.11/1.01      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.11/1.01      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.11/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.11/1.01      | l1_pre_topc(X1_53) != iProver_top ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_2381,c_29,c_30,c_31,c_36,c_37]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2516,plain,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51) = k9_relat_1(k3_tmap_1(X1_53,sK1,sK3,X0_53,sK4),X0_51)
% 2.11/1.01      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.11/1.01      | m1_pre_topc(sK3,X1_53) != iProver_top
% 2.11/1.01      | v2_struct_0(X1_53) = iProver_top
% 2.11/1.01      | v2_pre_topc(X1_53) != iProver_top
% 2.11/1.01      | l1_pre_topc(X1_53) != iProver_top ),
% 2.11/1.01      inference(renaming,[status(thm)],[c_2515]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2529,plain,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_51) = k9_relat_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_51)
% 2.11/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.11/1.01      | v2_struct_0(sK0) = iProver_top
% 2.11/1.01      | v2_pre_topc(sK0) != iProver_top
% 2.11/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_922,c_2516]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_35,plain,
% 2.11/1.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2665,plain,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_51) = k9_relat_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X0_51) ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_2529,c_26,c_27,c_28,c_35]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1698,plain,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_51) = k9_relat_1(sK4,X0_51) ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_917,c_909]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_9,negated_conjecture,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 2.11/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_458,negated_conjecture,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 2.11/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1826,plain,
% 2.11/1.01      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
% 2.11/1.01      inference(demodulation,[status(thm)],[c_1698,c_458]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2669,plain,
% 2.11/1.01      ( k9_relat_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
% 2.11/1.01      inference(demodulation,[status(thm)],[c_2665,c_1826]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3134,plain,
% 2.11/1.01      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 2.11/1.01      inference(demodulation,[status(thm)],[c_3130,c_2669]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_0,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.11/1.01      inference(cnf_transformation,[],[f28]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_466,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.11/1.01      | ~ v1_relat_1(X1_51)
% 2.11/1.01      | v1_relat_1(X0_51) ),
% 2.11/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_907,plain,
% 2.11/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 2.11/1.01      | v1_relat_1(X1_51) != iProver_top
% 2.11/1.01      | v1_relat_1(X0_51) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1506,plain,
% 2.11/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
% 2.11/1.01      | v1_relat_1(sK4) = iProver_top ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_917,c_907]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_38,plain,
% 2.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1147,plain,
% 2.11/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.11/1.01      | v1_relat_1(X0_51)
% 2.11/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1_51,X2_51)) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_466]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1315,plain,
% 2.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.11/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
% 2.11/1.01      | v1_relat_1(sK4) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_1147]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1316,plain,
% 2.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.11/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) != iProver_top
% 2.11/1.01      | v1_relat_1(sK4) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_1315]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1,plain,
% 2.11/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.11/1.01      inference(cnf_transformation,[],[f29]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_465,plain,
% 2.11/1.01      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 2.11/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1333,plain,
% 2.11/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
% 2.11/1.01      inference(instantiation,[status(thm)],[c_465]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1334,plain,
% 2.11/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) = iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1607,plain,
% 2.11/1.01      ( v1_relat_1(sK4) = iProver_top ),
% 2.11/1.01      inference(global_propositional_subsumption,
% 2.11/1.01                [status(thm)],
% 2.11/1.01                [c_1506,c_38,c_1316,c_1334]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_2,plain,
% 2.11/1.01      ( ~ r1_tarski(X0,X1)
% 2.11/1.01      | ~ v1_relat_1(X2)
% 2.11/1.01      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 2.11/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_10,negated_conjecture,
% 2.11/1.01      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.11/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_262,plain,
% 2.11/1.01      ( ~ v1_relat_1(X0)
% 2.11/1.01      | k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 2.11/1.01      | u1_struct_0(sK2) != X1
% 2.11/1.01      | sK5 != X2 ),
% 2.11/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_263,plain,
% 2.11/1.01      ( ~ v1_relat_1(X0)
% 2.11/1.01      | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
% 2.11/1.01      inference(unflattening,[status(thm)],[c_262]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_442,plain,
% 2.11/1.01      ( ~ v1_relat_1(X0_51)
% 2.11/1.01      | k9_relat_1(k7_relat_1(X0_51,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_51,sK5) ),
% 2.11/1.01      inference(subtyping,[status(esa)],[c_263]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_930,plain,
% 2.11/1.01      ( k9_relat_1(k7_relat_1(X0_51,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_51,sK5)
% 2.11/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 2.11/1.01      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_1615,plain,
% 2.11/1.01      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
% 2.11/1.01      inference(superposition,[status(thm)],[c_1607,c_930]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3139,plain,
% 2.11/1.01      ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
% 2.11/1.01      inference(light_normalisation,[status(thm)],[c_3134,c_1615]) ).
% 2.11/1.01  
% 2.11/1.01  cnf(c_3140,plain,
% 2.11/1.01      ( $false ),
% 2.11/1.01      inference(equality_resolution_simp,[status(thm)],[c_3139]) ).
% 2.11/1.01  
% 2.11/1.01  
% 2.11/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/1.01  
% 2.11/1.01  ------                               Statistics
% 2.11/1.01  
% 2.11/1.01  ------ General
% 2.11/1.01  
% 2.11/1.01  abstr_ref_over_cycles:                  0
% 2.11/1.01  abstr_ref_under_cycles:                 0
% 2.11/1.01  gc_basic_clause_elim:                   0
% 2.11/1.01  forced_gc_time:                         0
% 2.11/1.01  parsing_time:                           0.008
% 2.11/1.01  unif_index_cands_time:                  0.
% 2.11/1.01  unif_index_add_time:                    0.
% 2.11/1.01  orderings_time:                         0.
% 2.11/1.01  out_proof_time:                         0.012
% 2.11/1.01  total_time:                             0.187
% 2.11/1.01  num_of_symbols:                         58
% 2.11/1.01  num_of_terms:                           3088
% 2.11/1.01  
% 2.11/1.01  ------ Preprocessing
% 2.11/1.01  
% 2.11/1.01  num_of_splits:                          0
% 2.11/1.01  num_of_split_atoms:                     0
% 2.11/1.01  num_of_reused_defs:                     0
% 2.11/1.01  num_eq_ax_congr_red:                    18
% 2.11/1.01  num_of_sem_filtered_clauses:            1
% 2.11/1.01  num_of_subtypes:                        4
% 2.11/1.01  monotx_restored_types:                  0
% 2.11/1.01  sat_num_of_epr_types:                   0
% 2.11/1.01  sat_num_of_non_cyclic_types:            0
% 2.11/1.01  sat_guarded_non_collapsed_types:        0
% 2.11/1.01  num_pure_diseq_elim:                    0
% 2.11/1.01  simp_replaced_by:                       0
% 2.11/1.01  res_preprocessed:                       134
% 2.11/1.01  prep_upred:                             0
% 2.11/1.01  prep_unflattend:                        2
% 2.11/1.01  smt_new_axioms:                         0
% 2.11/1.01  pred_elim_cands:                        8
% 2.11/1.01  pred_elim:                              1
% 2.11/1.01  pred_elim_cl:                           1
% 2.11/1.01  pred_elim_cycles:                       3
% 2.11/1.01  merged_defs:                            0
% 2.11/1.01  merged_defs_ncl:                        0
% 2.11/1.01  bin_hyper_res:                          0
% 2.11/1.01  prep_cycles:                            4
% 2.11/1.01  pred_elim_time:                         0.001
% 2.11/1.01  splitting_time:                         0.
% 2.11/1.01  sem_filter_time:                        0.
% 2.11/1.01  monotx_time:                            0.
% 2.11/1.01  subtype_inf_time:                       0.
% 2.11/1.01  
% 2.11/1.01  ------ Problem properties
% 2.11/1.01  
% 2.11/1.01  clauses:                                25
% 2.11/1.01  conjectures:                            16
% 2.11/1.01  epr:                                    12
% 2.11/1.01  horn:                                   21
% 2.11/1.01  ground:                                 16
% 2.11/1.01  unary:                                  17
% 2.11/1.01  binary:                                 2
% 2.11/1.01  lits:                                   76
% 2.11/1.01  lits_eq:                                5
% 2.11/1.01  fd_pure:                                0
% 2.11/1.01  fd_pseudo:                              0
% 2.11/1.01  fd_cond:                                0
% 2.11/1.01  fd_pseudo_cond:                         0
% 2.11/1.01  ac_symbols:                             0
% 2.11/1.01  
% 2.11/1.01  ------ Propositional Solver
% 2.11/1.01  
% 2.11/1.01  prop_solver_calls:                      27
% 2.11/1.01  prop_fast_solver_calls:                 1096
% 2.11/1.01  smt_solver_calls:                       0
% 2.11/1.01  smt_fast_solver_calls:                  0
% 2.11/1.01  prop_num_of_clauses:                    1004
% 2.11/1.01  prop_preprocess_simplified:             3739
% 2.11/1.01  prop_fo_subsumed:                       40
% 2.11/1.01  prop_solver_time:                       0.
% 2.11/1.01  smt_solver_time:                        0.
% 2.11/1.01  smt_fast_solver_time:                   0.
% 2.11/1.01  prop_fast_solver_time:                  0.
% 2.11/1.01  prop_unsat_core_time:                   0.
% 2.11/1.01  
% 2.11/1.01  ------ QBF
% 2.11/1.01  
% 2.11/1.01  qbf_q_res:                              0
% 2.11/1.01  qbf_num_tautologies:                    0
% 2.11/1.01  qbf_prep_cycles:                        0
% 2.11/1.01  
% 2.11/1.01  ------ BMC1
% 2.11/1.01  
% 2.11/1.01  bmc1_current_bound:                     -1
% 2.11/1.01  bmc1_last_solved_bound:                 -1
% 2.11/1.01  bmc1_unsat_core_size:                   -1
% 2.11/1.01  bmc1_unsat_core_parents_size:           -1
% 2.11/1.01  bmc1_merge_next_fun:                    0
% 2.11/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.11/1.01  
% 2.11/1.01  ------ Instantiation
% 2.11/1.01  
% 2.11/1.01  inst_num_of_clauses:                    325
% 2.11/1.01  inst_num_in_passive:                    75
% 2.11/1.01  inst_num_in_active:                     233
% 2.11/1.01  inst_num_in_unprocessed:                17
% 2.11/1.01  inst_num_of_loops:                      250
% 2.11/1.01  inst_num_of_learning_restarts:          0
% 2.11/1.01  inst_num_moves_active_passive:          12
% 2.11/1.01  inst_lit_activity:                      0
% 2.11/1.01  inst_lit_activity_moves:                0
% 2.11/1.01  inst_num_tautologies:                   0
% 2.11/1.01  inst_num_prop_implied:                  0
% 2.11/1.01  inst_num_existing_simplified:           0
% 2.11/1.01  inst_num_eq_res_simplified:             0
% 2.11/1.01  inst_num_child_elim:                    0
% 2.11/1.01  inst_num_of_dismatching_blockings:      46
% 2.11/1.01  inst_num_of_non_proper_insts:           296
% 2.11/1.01  inst_num_of_duplicates:                 0
% 2.11/1.01  inst_inst_num_from_inst_to_res:         0
% 2.11/1.01  inst_dismatching_checking_time:         0.
% 2.11/1.01  
% 2.11/1.01  ------ Resolution
% 2.11/1.01  
% 2.11/1.01  res_num_of_clauses:                     0
% 2.11/1.01  res_num_in_passive:                     0
% 2.11/1.01  res_num_in_active:                      0
% 2.11/1.01  res_num_of_loops:                       138
% 2.11/1.01  res_forward_subset_subsumed:            55
% 2.11/1.01  res_backward_subset_subsumed:           0
% 2.11/1.01  res_forward_subsumed:                   0
% 2.11/1.01  res_backward_subsumed:                  0
% 2.11/1.01  res_forward_subsumption_resolution:     0
% 2.11/1.01  res_backward_subsumption_resolution:    0
% 2.11/1.01  res_clause_to_clause_subsumption:       153
% 2.11/1.01  res_orphan_elimination:                 0
% 2.11/1.01  res_tautology_del:                      39
% 2.11/1.01  res_num_eq_res_simplified:              0
% 2.11/1.01  res_num_sel_changes:                    0
% 2.11/1.01  res_moves_from_active_to_pass:          0
% 2.11/1.01  
% 2.11/1.01  ------ Superposition
% 2.11/1.01  
% 2.11/1.01  sup_time_total:                         0.
% 2.11/1.01  sup_time_generating:                    0.
% 2.11/1.01  sup_time_sim_full:                      0.
% 2.11/1.01  sup_time_sim_immed:                     0.
% 2.11/1.01  
% 2.11/1.01  sup_num_of_clauses:                     49
% 2.11/1.01  sup_num_in_active:                      44
% 2.11/1.01  sup_num_in_passive:                     5
% 2.11/1.01  sup_num_of_loops:                       49
% 2.11/1.01  sup_fw_superposition:                   19
% 2.11/1.01  sup_bw_superposition:                   8
% 2.11/1.01  sup_immediate_simplified:               1
% 2.11/1.01  sup_given_eliminated:                   0
% 2.11/1.01  comparisons_done:                       0
% 2.11/1.01  comparisons_avoided:                    0
% 2.11/1.01  
% 2.11/1.01  ------ Simplifications
% 2.11/1.01  
% 2.11/1.01  
% 2.11/1.01  sim_fw_subset_subsumed:                 0
% 2.11/1.01  sim_bw_subset_subsumed:                 0
% 2.11/1.01  sim_fw_subsumed:                        0
% 2.11/1.01  sim_bw_subsumed:                        0
% 2.11/1.01  sim_fw_subsumption_res:                 1
% 2.11/1.01  sim_bw_subsumption_res:                 0
% 2.11/1.01  sim_tautology_del:                      0
% 2.11/1.01  sim_eq_tautology_del:                   0
% 2.11/1.01  sim_eq_res_simp:                        0
% 2.11/1.01  sim_fw_demodulated:                     1
% 2.11/1.01  sim_bw_demodulated:                     5
% 2.11/1.01  sim_light_normalised:                   1
% 2.11/1.01  sim_joinable_taut:                      0
% 2.11/1.01  sim_joinable_simp:                      0
% 2.11/1.01  sim_ac_normalised:                      0
% 2.11/1.01  sim_smt_subsumption:                    0
% 2.11/1.01  
%------------------------------------------------------------------------------
