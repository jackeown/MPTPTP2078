%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:55 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 689 expanded)
%              Number of clauses        :  109 ( 175 expanded)
%              Number of leaves         :   17 ( 300 expanded)
%              Depth                    :   21
%              Number of atoms          :  999 (9445 expanded)
%              Number of equality atoms :  345 (1085 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   34 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f17])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & r1_tarski(X5,u1_struct_0(X2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & r1_tarski(sK5,u1_struct_0(X2))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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

fof(f22,plain,(
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

fof(f21,plain,(
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

fof(f20,plain,(
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

fof(f19,plain,
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

fof(f25,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f24,f23,f22,f21,f20,f19])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f13])).

fof(f29,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(X4,u1_struct_0(X2))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ~ r1_tarski(X4,u1_struct_0(X2))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ~ r1_tarski(X4,u1_struct_0(X2))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | ~ r1_tarski(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_548,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_862,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_317,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_11,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_321,plain,
    ( v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_11])).

cnf(c_322,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_321])).

cnf(c_539,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X3_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,sK4) ),
    inference(subtyping,[status(esa)],[c_322])).

cnf(c_871,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X0_52,X1_52,X2_52,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_pre_topc(X2_52,X1_52) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_pre_topc(X1_52,X3_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_1431,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_871])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_26,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_27,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_560,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1036,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1037,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X2_52,X1_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X2_52)) = k3_tmap_1(X1_52,sK1,X0_52,X2_52,sK4) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_1041,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_1611,plain,
    ( v2_pre_topc(X2_52) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK4)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | l1_pre_topc(X2_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1431,c_25,c_26,c_27,c_1036,c_1041])).

cnf(c_1612,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_1611])).

cnf(c_1624,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK3,X0_52,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1612])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1774,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK3,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1624,c_34])).

cnf(c_1789,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_1774])).

cnf(c_8,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_552,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_858,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_368,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_372,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_11])).

cnf(c_373,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_538,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_pre_topc(X2_52,X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,sK4,X2_52) ),
    inference(subtyping,[status(esa)],[c_373])).

cnf(c_872,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,u1_struct_0(X2_52)) = k2_tmap_1(X1_52,X0_52,sK4,X2_52)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | m1_pre_topc(X2_52,X1_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_1365,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_872])).

cnf(c_1038,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
    | ~ m1_pre_topc(X1_52,X0_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK1)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1039,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1038])).

cnf(c_1549,plain,
    ( v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1365,c_25,c_26,c_27,c_1036,c_1039])).

cnf(c_1550,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_1549])).

cnf(c_1560,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK1,sK4,X0_52)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_52,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1550])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_23,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_30,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_31,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_550,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_860,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_556,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v2_pre_topc(X1_52)
    | v2_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_855,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_1132,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_860,c_855])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_555,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1093,plain,
    ( ~ m1_pre_topc(sK3,X0_52)
    | ~ l1_pre_topc(X0_52)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_1191,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1192,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1191])).

cnf(c_1692,plain,
    ( m1_pre_topc(X0_52,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK1,sK4,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_23,c_24,c_30,c_31,c_34,c_1132,c_1192])).

cnf(c_1693,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK1,sK4,X0_52)
    | m1_pre_topc(X0_52,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_1692])).

cnf(c_1700,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_858,c_1693])).

cnf(c_1796,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1789,c_1700])).

cnf(c_571,plain,
    ( k7_relset_1(X0_51,X1_51,X0_49,X1_49) = k7_relset_1(X2_51,X3_51,X2_49,X3_49)
    | X0_51 != X2_51
    | X1_51 != X3_51
    | X0_49 != X2_49
    | X1_49 != X3_49 ),
    theory(equality)).

cnf(c_1659,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k2_tmap_1(sK3,sK1,sK4,sK2)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_564,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_1121,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != X0_53
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X0_53 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_1575,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1069,plain,
    ( X0_53 != X1_53
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X1_53
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_1204,plain,
    ( X0_53 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_53
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1331,plain,
    ( k7_relset_1(X0_51,X1_51,X0_49,X1_49) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(X0_51,X1_51,X0_49,X1_49)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_1528,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_1308,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tarski(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X4,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | k7_relset_1(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,X4),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_213,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X4,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k7_relset_1(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,X4),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
    | u1_struct_0(X4) != u1_struct_0(sK2)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_214,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,X3),sK5) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK5)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,X3),sK5) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK5)
    | u1_struct_0(X3) != u1_struct_0(sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_214,c_10])).

cnf(c_263,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),sK5) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK5)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_267,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),sK5) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK5)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_11])).

cnf(c_268,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),sK5) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK5)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_267])).

cnf(c_540,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_pre_topc(X2_52,X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | k7_relset_1(u1_struct_0(X2_52),u1_struct_0(X1_52),k2_tmap_1(X0_52,X1_52,sK4,X2_52),sK5) = k7_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,sK5)
    | u1_struct_0(X2_52) != u1_struct_0(sK2)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(X0_52) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_268])).

cnf(c_1031,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
    | ~ m1_pre_topc(X1_52,sK3)
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK3)
    | k7_relset_1(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK3,X0_52,sK4,X1_52),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0_52),sK4,sK5)
    | u1_struct_0(X1_52) != u1_struct_0(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_1283,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
    | ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK3)
    | k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_52),k2_tmap_1(sK3,X0_52,sK4,sK2),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0_52),sK4,sK5)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_1284,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_52),k2_tmap_1(sK3,X0_52,sK4,sK2),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0_52),sK4,sK5)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1283])).

cnf(c_1286,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1284])).

cnf(c_1105,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_558,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1075,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_561,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1068,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_1048,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != X0_53
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X0_53
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_1067,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_5,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_554,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_35,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_22,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1796,c_1659,c_1575,c_1528,c_1308,c_1286,c_1192,c_1132,c_1105,c_1075,c_1068,c_1067,c_1036,c_554,c_36,c_35,c_34,c_31,c_30,c_28,c_27,c_26,c_25,c_24,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:01:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.61/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/0.99  
% 1.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.61/0.99  
% 1.61/0.99  ------  iProver source info
% 1.61/0.99  
% 1.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.61/0.99  git: non_committed_changes: false
% 1.61/0.99  git: last_make_outside_of_git: false
% 1.61/0.99  
% 1.61/0.99  ------ 
% 1.61/0.99  
% 1.61/0.99  ------ Input Options
% 1.61/0.99  
% 1.61/0.99  --out_options                           all
% 1.61/0.99  --tptp_safe_out                         true
% 1.61/0.99  --problem_path                          ""
% 1.61/0.99  --include_path                          ""
% 1.61/0.99  --clausifier                            res/vclausify_rel
% 1.61/0.99  --clausifier_options                    --mode clausify
% 1.61/0.99  --stdin                                 false
% 1.61/0.99  --stats_out                             all
% 1.61/0.99  
% 1.61/0.99  ------ General Options
% 1.61/0.99  
% 1.61/0.99  --fof                                   false
% 1.61/0.99  --time_out_real                         305.
% 1.61/0.99  --time_out_virtual                      -1.
% 1.61/0.99  --symbol_type_check                     false
% 1.61/0.99  --clausify_out                          false
% 1.61/0.99  --sig_cnt_out                           false
% 1.61/0.99  --trig_cnt_out                          false
% 1.61/0.99  --trig_cnt_out_tolerance                1.
% 1.61/0.99  --trig_cnt_out_sk_spl                   false
% 1.61/0.99  --abstr_cl_out                          false
% 1.61/0.99  
% 1.61/0.99  ------ Global Options
% 1.61/0.99  
% 1.61/0.99  --schedule                              default
% 1.61/0.99  --add_important_lit                     false
% 1.61/0.99  --prop_solver_per_cl                    1000
% 1.61/0.99  --min_unsat_core                        false
% 1.61/0.99  --soft_assumptions                      false
% 1.61/0.99  --soft_lemma_size                       3
% 1.61/0.99  --prop_impl_unit_size                   0
% 1.61/0.99  --prop_impl_unit                        []
% 1.61/0.99  --share_sel_clauses                     true
% 1.61/0.99  --reset_solvers                         false
% 1.61/0.99  --bc_imp_inh                            [conj_cone]
% 1.61/0.99  --conj_cone_tolerance                   3.
% 1.61/0.99  --extra_neg_conj                        none
% 1.61/0.99  --large_theory_mode                     true
% 1.61/0.99  --prolific_symb_bound                   200
% 1.61/0.99  --lt_threshold                          2000
% 1.61/0.99  --clause_weak_htbl                      true
% 1.61/0.99  --gc_record_bc_elim                     false
% 1.61/0.99  
% 1.61/0.99  ------ Preprocessing Options
% 1.61/0.99  
% 1.61/0.99  --preprocessing_flag                    true
% 1.61/0.99  --time_out_prep_mult                    0.1
% 1.61/0.99  --splitting_mode                        input
% 1.61/0.99  --splitting_grd                         true
% 1.61/0.99  --splitting_cvd                         false
% 1.61/0.99  --splitting_cvd_svl                     false
% 1.61/0.99  --splitting_nvd                         32
% 1.61/0.99  --sub_typing                            true
% 1.61/0.99  --prep_gs_sim                           true
% 1.61/0.99  --prep_unflatten                        true
% 1.61/0.99  --prep_res_sim                          true
% 1.61/0.99  --prep_upred                            true
% 1.61/0.99  --prep_sem_filter                       exhaustive
% 1.61/0.99  --prep_sem_filter_out                   false
% 1.61/0.99  --pred_elim                             true
% 1.61/0.99  --res_sim_input                         true
% 1.61/0.99  --eq_ax_congr_red                       true
% 1.61/0.99  --pure_diseq_elim                       true
% 1.61/0.99  --brand_transform                       false
% 1.61/0.99  --non_eq_to_eq                          false
% 1.61/0.99  --prep_def_merge                        true
% 1.61/0.99  --prep_def_merge_prop_impl              false
% 1.61/0.99  --prep_def_merge_mbd                    true
% 1.61/0.99  --prep_def_merge_tr_red                 false
% 1.61/0.99  --prep_def_merge_tr_cl                  false
% 1.61/0.99  --smt_preprocessing                     true
% 1.61/0.99  --smt_ac_axioms                         fast
% 1.61/0.99  --preprocessed_out                      false
% 1.61/0.99  --preprocessed_stats                    false
% 1.61/0.99  
% 1.61/0.99  ------ Abstraction refinement Options
% 1.61/0.99  
% 1.61/0.99  --abstr_ref                             []
% 1.61/0.99  --abstr_ref_prep                        false
% 1.61/0.99  --abstr_ref_until_sat                   false
% 1.61/0.99  --abstr_ref_sig_restrict                funpre
% 1.61/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.61/0.99  --abstr_ref_under                       []
% 1.61/0.99  
% 1.61/0.99  ------ SAT Options
% 1.61/0.99  
% 1.61/0.99  --sat_mode                              false
% 1.61/0.99  --sat_fm_restart_options                ""
% 1.61/0.99  --sat_gr_def                            false
% 1.61/0.99  --sat_epr_types                         true
% 1.61/0.99  --sat_non_cyclic_types                  false
% 1.61/0.99  --sat_finite_models                     false
% 1.61/0.99  --sat_fm_lemmas                         false
% 1.61/0.99  --sat_fm_prep                           false
% 1.61/0.99  --sat_fm_uc_incr                        true
% 1.61/0.99  --sat_out_model                         small
% 1.61/0.99  --sat_out_clauses                       false
% 1.61/0.99  
% 1.61/0.99  ------ QBF Options
% 1.61/0.99  
% 1.61/0.99  --qbf_mode                              false
% 1.61/0.99  --qbf_elim_univ                         false
% 1.61/0.99  --qbf_dom_inst                          none
% 1.61/0.99  --qbf_dom_pre_inst                      false
% 1.61/0.99  --qbf_sk_in                             false
% 1.61/0.99  --qbf_pred_elim                         true
% 1.61/0.99  --qbf_split                             512
% 1.61/0.99  
% 1.61/0.99  ------ BMC1 Options
% 1.61/0.99  
% 1.61/0.99  --bmc1_incremental                      false
% 1.61/0.99  --bmc1_axioms                           reachable_all
% 1.61/0.99  --bmc1_min_bound                        0
% 1.61/0.99  --bmc1_max_bound                        -1
% 1.61/0.99  --bmc1_max_bound_default                -1
% 1.61/0.99  --bmc1_symbol_reachability              true
% 1.61/0.99  --bmc1_property_lemmas                  false
% 1.61/0.99  --bmc1_k_induction                      false
% 1.61/0.99  --bmc1_non_equiv_states                 false
% 1.61/0.99  --bmc1_deadlock                         false
% 1.61/0.99  --bmc1_ucm                              false
% 1.61/0.99  --bmc1_add_unsat_core                   none
% 1.61/0.99  --bmc1_unsat_core_children              false
% 1.61/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.61/0.99  --bmc1_out_stat                         full
% 1.61/0.99  --bmc1_ground_init                      false
% 1.61/0.99  --bmc1_pre_inst_next_state              false
% 1.61/0.99  --bmc1_pre_inst_state                   false
% 1.61/0.99  --bmc1_pre_inst_reach_state             false
% 1.61/0.99  --bmc1_out_unsat_core                   false
% 1.61/0.99  --bmc1_aig_witness_out                  false
% 1.61/0.99  --bmc1_verbose                          false
% 1.61/0.99  --bmc1_dump_clauses_tptp                false
% 1.61/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.61/0.99  --bmc1_dump_file                        -
% 1.61/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.61/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.61/0.99  --bmc1_ucm_extend_mode                  1
% 1.61/0.99  --bmc1_ucm_init_mode                    2
% 1.61/0.99  --bmc1_ucm_cone_mode                    none
% 1.61/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.61/0.99  --bmc1_ucm_relax_model                  4
% 1.61/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.61/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.61/0.99  --bmc1_ucm_layered_model                none
% 1.61/0.99  --bmc1_ucm_max_lemma_size               10
% 1.61/0.99  
% 1.61/0.99  ------ AIG Options
% 1.61/0.99  
% 1.61/0.99  --aig_mode                              false
% 1.61/0.99  
% 1.61/0.99  ------ Instantiation Options
% 1.61/0.99  
% 1.61/0.99  --instantiation_flag                    true
% 1.61/0.99  --inst_sos_flag                         false
% 1.61/0.99  --inst_sos_phase                        true
% 1.61/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.61/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.61/0.99  --inst_lit_sel_side                     num_symb
% 1.61/0.99  --inst_solver_per_active                1400
% 1.61/0.99  --inst_solver_calls_frac                1.
% 1.61/0.99  --inst_passive_queue_type               priority_queues
% 1.61/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.61/0.99  --inst_passive_queues_freq              [25;2]
% 1.61/0.99  --inst_dismatching                      true
% 1.61/0.99  --inst_eager_unprocessed_to_passive     true
% 1.61/0.99  --inst_prop_sim_given                   true
% 1.61/0.99  --inst_prop_sim_new                     false
% 1.61/0.99  --inst_subs_new                         false
% 1.61/0.99  --inst_eq_res_simp                      false
% 1.61/0.99  --inst_subs_given                       false
% 1.61/0.99  --inst_orphan_elimination               true
% 1.61/0.99  --inst_learning_loop_flag               true
% 1.61/0.99  --inst_learning_start                   3000
% 1.61/0.99  --inst_learning_factor                  2
% 1.61/0.99  --inst_start_prop_sim_after_learn       3
% 1.61/0.99  --inst_sel_renew                        solver
% 1.61/0.99  --inst_lit_activity_flag                true
% 1.61/0.99  --inst_restr_to_given                   false
% 1.61/0.99  --inst_activity_threshold               500
% 1.61/0.99  --inst_out_proof                        true
% 1.61/0.99  
% 1.61/0.99  ------ Resolution Options
% 1.61/0.99  
% 1.61/0.99  --resolution_flag                       true
% 1.61/0.99  --res_lit_sel                           adaptive
% 1.61/0.99  --res_lit_sel_side                      none
% 1.61/0.99  --res_ordering                          kbo
% 1.61/0.99  --res_to_prop_solver                    active
% 1.61/0.99  --res_prop_simpl_new                    false
% 1.61/0.99  --res_prop_simpl_given                  true
% 1.61/0.99  --res_passive_queue_type                priority_queues
% 1.61/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.61/0.99  --res_passive_queues_freq               [15;5]
% 1.61/0.99  --res_forward_subs                      full
% 1.61/0.99  --res_backward_subs                     full
% 1.61/0.99  --res_forward_subs_resolution           true
% 1.61/0.99  --res_backward_subs_resolution          true
% 1.61/0.99  --res_orphan_elimination                true
% 1.61/0.99  --res_time_limit                        2.
% 1.61/0.99  --res_out_proof                         true
% 1.61/0.99  
% 1.61/0.99  ------ Superposition Options
% 1.61/0.99  
% 1.61/0.99  --superposition_flag                    true
% 1.61/0.99  --sup_passive_queue_type                priority_queues
% 1.61/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.61/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.61/0.99  --demod_completeness_check              fast
% 1.61/0.99  --demod_use_ground                      true
% 1.61/0.99  --sup_to_prop_solver                    passive
% 1.61/0.99  --sup_prop_simpl_new                    true
% 1.61/0.99  --sup_prop_simpl_given                  true
% 1.61/0.99  --sup_fun_splitting                     false
% 1.61/0.99  --sup_smt_interval                      50000
% 1.61/0.99  
% 1.61/0.99  ------ Superposition Simplification Setup
% 1.61/0.99  
% 1.61/0.99  --sup_indices_passive                   []
% 1.61/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.61/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.99  --sup_full_bw                           [BwDemod]
% 1.61/0.99  --sup_immed_triv                        [TrivRules]
% 1.61/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.61/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.99  --sup_immed_bw_main                     []
% 1.61/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.61/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/0.99  
% 1.61/0.99  ------ Combination Options
% 1.61/0.99  
% 1.61/0.99  --comb_res_mult                         3
% 1.61/0.99  --comb_sup_mult                         2
% 1.61/0.99  --comb_inst_mult                        10
% 1.61/0.99  
% 1.61/0.99  ------ Debug Options
% 1.61/0.99  
% 1.61/0.99  --dbg_backtrace                         false
% 1.61/0.99  --dbg_dump_prop_clauses                 false
% 1.61/0.99  --dbg_dump_prop_clauses_file            -
% 1.61/0.99  --dbg_out_stat                          false
% 1.61/0.99  ------ Parsing...
% 1.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.61/0.99  
% 1.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.61/0.99  
% 1.61/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.61/0.99  
% 1.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.61/0.99  ------ Proving...
% 1.61/0.99  ------ Problem Properties 
% 1.61/0.99  
% 1.61/0.99  
% 1.61/0.99  clauses                                 19
% 1.61/0.99  conjectures                             14
% 1.61/0.99  EPR                                     13
% 1.61/0.99  Horn                                    16
% 1.61/0.99  unary                                   14
% 1.61/0.99  binary                                  0
% 1.61/0.99  lits                                    59
% 1.61/0.99  lits eq                                 11
% 1.61/0.99  fd_pure                                 0
% 1.61/0.99  fd_pseudo                               0
% 1.61/0.99  fd_cond                                 0
% 1.61/0.99  fd_pseudo_cond                          0
% 1.61/0.99  AC symbols                              0
% 1.61/0.99  
% 1.61/0.99  ------ Schedule dynamic 5 is on 
% 1.61/0.99  
% 1.61/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.61/0.99  
% 1.61/0.99  
% 1.61/0.99  ------ 
% 1.61/0.99  Current options:
% 1.61/0.99  ------ 
% 1.61/0.99  
% 1.61/0.99  ------ Input Options
% 1.61/0.99  
% 1.61/0.99  --out_options                           all
% 1.61/0.99  --tptp_safe_out                         true
% 1.61/0.99  --problem_path                          ""
% 1.61/0.99  --include_path                          ""
% 1.61/0.99  --clausifier                            res/vclausify_rel
% 1.61/0.99  --clausifier_options                    --mode clausify
% 1.61/0.99  --stdin                                 false
% 1.61/0.99  --stats_out                             all
% 1.61/0.99  
% 1.61/0.99  ------ General Options
% 1.61/0.99  
% 1.61/0.99  --fof                                   false
% 1.61/0.99  --time_out_real                         305.
% 1.61/0.99  --time_out_virtual                      -1.
% 1.61/0.99  --symbol_type_check                     false
% 1.61/0.99  --clausify_out                          false
% 1.61/0.99  --sig_cnt_out                           false
% 1.61/0.99  --trig_cnt_out                          false
% 1.61/0.99  --trig_cnt_out_tolerance                1.
% 1.61/0.99  --trig_cnt_out_sk_spl                   false
% 1.61/0.99  --abstr_cl_out                          false
% 1.61/0.99  
% 1.61/0.99  ------ Global Options
% 1.61/0.99  
% 1.61/0.99  --schedule                              default
% 1.61/0.99  --add_important_lit                     false
% 1.61/0.99  --prop_solver_per_cl                    1000
% 1.61/0.99  --min_unsat_core                        false
% 1.61/0.99  --soft_assumptions                      false
% 1.61/0.99  --soft_lemma_size                       3
% 1.61/0.99  --prop_impl_unit_size                   0
% 1.61/0.99  --prop_impl_unit                        []
% 1.61/0.99  --share_sel_clauses                     true
% 1.61/0.99  --reset_solvers                         false
% 1.61/0.99  --bc_imp_inh                            [conj_cone]
% 1.61/0.99  --conj_cone_tolerance                   3.
% 1.61/0.99  --extra_neg_conj                        none
% 1.61/0.99  --large_theory_mode                     true
% 1.61/0.99  --prolific_symb_bound                   200
% 1.61/0.99  --lt_threshold                          2000
% 1.61/0.99  --clause_weak_htbl                      true
% 1.61/0.99  --gc_record_bc_elim                     false
% 1.61/0.99  
% 1.61/0.99  ------ Preprocessing Options
% 1.61/0.99  
% 1.61/0.99  --preprocessing_flag                    true
% 1.61/0.99  --time_out_prep_mult                    0.1
% 1.61/0.99  --splitting_mode                        input
% 1.61/0.99  --splitting_grd                         true
% 1.61/0.99  --splitting_cvd                         false
% 1.61/0.99  --splitting_cvd_svl                     false
% 1.61/0.99  --splitting_nvd                         32
% 1.61/0.99  --sub_typing                            true
% 1.61/0.99  --prep_gs_sim                           true
% 1.61/0.99  --prep_unflatten                        true
% 1.61/0.99  --prep_res_sim                          true
% 1.61/0.99  --prep_upred                            true
% 1.61/0.99  --prep_sem_filter                       exhaustive
% 1.61/0.99  --prep_sem_filter_out                   false
% 1.61/0.99  --pred_elim                             true
% 1.61/0.99  --res_sim_input                         true
% 1.61/0.99  --eq_ax_congr_red                       true
% 1.61/0.99  --pure_diseq_elim                       true
% 1.61/0.99  --brand_transform                       false
% 1.61/0.99  --non_eq_to_eq                          false
% 1.61/0.99  --prep_def_merge                        true
% 1.61/0.99  --prep_def_merge_prop_impl              false
% 1.61/0.99  --prep_def_merge_mbd                    true
% 1.61/0.99  --prep_def_merge_tr_red                 false
% 1.61/0.99  --prep_def_merge_tr_cl                  false
% 1.61/0.99  --smt_preprocessing                     true
% 1.61/0.99  --smt_ac_axioms                         fast
% 1.61/0.99  --preprocessed_out                      false
% 1.61/0.99  --preprocessed_stats                    false
% 1.61/0.99  
% 1.61/0.99  ------ Abstraction refinement Options
% 1.61/0.99  
% 1.61/0.99  --abstr_ref                             []
% 1.61/0.99  --abstr_ref_prep                        false
% 1.61/0.99  --abstr_ref_until_sat                   false
% 1.61/0.99  --abstr_ref_sig_restrict                funpre
% 1.61/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.61/0.99  --abstr_ref_under                       []
% 1.61/0.99  
% 1.61/0.99  ------ SAT Options
% 1.61/0.99  
% 1.61/0.99  --sat_mode                              false
% 1.61/0.99  --sat_fm_restart_options                ""
% 1.61/0.99  --sat_gr_def                            false
% 1.61/0.99  --sat_epr_types                         true
% 1.61/0.99  --sat_non_cyclic_types                  false
% 1.61/0.99  --sat_finite_models                     false
% 1.61/0.99  --sat_fm_lemmas                         false
% 1.61/0.99  --sat_fm_prep                           false
% 1.61/0.99  --sat_fm_uc_incr                        true
% 1.61/0.99  --sat_out_model                         small
% 1.61/0.99  --sat_out_clauses                       false
% 1.61/0.99  
% 1.61/0.99  ------ QBF Options
% 1.61/0.99  
% 1.61/0.99  --qbf_mode                              false
% 1.61/0.99  --qbf_elim_univ                         false
% 1.61/0.99  --qbf_dom_inst                          none
% 1.61/0.99  --qbf_dom_pre_inst                      false
% 1.61/0.99  --qbf_sk_in                             false
% 1.61/0.99  --qbf_pred_elim                         true
% 1.61/0.99  --qbf_split                             512
% 1.61/0.99  
% 1.61/0.99  ------ BMC1 Options
% 1.61/0.99  
% 1.61/0.99  --bmc1_incremental                      false
% 1.61/0.99  --bmc1_axioms                           reachable_all
% 1.61/0.99  --bmc1_min_bound                        0
% 1.61/0.99  --bmc1_max_bound                        -1
% 1.61/0.99  --bmc1_max_bound_default                -1
% 1.61/0.99  --bmc1_symbol_reachability              true
% 1.61/0.99  --bmc1_property_lemmas                  false
% 1.61/0.99  --bmc1_k_induction                      false
% 1.61/0.99  --bmc1_non_equiv_states                 false
% 1.61/0.99  --bmc1_deadlock                         false
% 1.61/0.99  --bmc1_ucm                              false
% 1.61/0.99  --bmc1_add_unsat_core                   none
% 1.61/0.99  --bmc1_unsat_core_children              false
% 1.61/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.61/0.99  --bmc1_out_stat                         full
% 1.61/0.99  --bmc1_ground_init                      false
% 1.61/0.99  --bmc1_pre_inst_next_state              false
% 1.61/0.99  --bmc1_pre_inst_state                   false
% 1.61/0.99  --bmc1_pre_inst_reach_state             false
% 1.61/0.99  --bmc1_out_unsat_core                   false
% 1.61/0.99  --bmc1_aig_witness_out                  false
% 1.61/0.99  --bmc1_verbose                          false
% 1.61/0.99  --bmc1_dump_clauses_tptp                false
% 1.61/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.61/0.99  --bmc1_dump_file                        -
% 1.61/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.61/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.61/0.99  --bmc1_ucm_extend_mode                  1
% 1.61/0.99  --bmc1_ucm_init_mode                    2
% 1.61/0.99  --bmc1_ucm_cone_mode                    none
% 1.61/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.61/0.99  --bmc1_ucm_relax_model                  4
% 1.61/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.61/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.61/0.99  --bmc1_ucm_layered_model                none
% 1.61/0.99  --bmc1_ucm_max_lemma_size               10
% 1.61/0.99  
% 1.61/0.99  ------ AIG Options
% 1.61/0.99  
% 1.61/0.99  --aig_mode                              false
% 1.61/0.99  
% 1.61/0.99  ------ Instantiation Options
% 1.61/0.99  
% 1.61/0.99  --instantiation_flag                    true
% 1.61/0.99  --inst_sos_flag                         false
% 1.61/0.99  --inst_sos_phase                        true
% 1.61/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.61/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.61/0.99  --inst_lit_sel_side                     none
% 1.61/0.99  --inst_solver_per_active                1400
% 1.61/0.99  --inst_solver_calls_frac                1.
% 1.61/0.99  --inst_passive_queue_type               priority_queues
% 1.61/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.61/0.99  --inst_passive_queues_freq              [25;2]
% 1.61/0.99  --inst_dismatching                      true
% 1.61/0.99  --inst_eager_unprocessed_to_passive     true
% 1.61/0.99  --inst_prop_sim_given                   true
% 1.61/0.99  --inst_prop_sim_new                     false
% 1.61/0.99  --inst_subs_new                         false
% 1.61/0.99  --inst_eq_res_simp                      false
% 1.61/0.99  --inst_subs_given                       false
% 1.61/0.99  --inst_orphan_elimination               true
% 1.61/0.99  --inst_learning_loop_flag               true
% 1.61/0.99  --inst_learning_start                   3000
% 1.61/0.99  --inst_learning_factor                  2
% 1.61/0.99  --inst_start_prop_sim_after_learn       3
% 1.61/0.99  --inst_sel_renew                        solver
% 1.61/0.99  --inst_lit_activity_flag                true
% 1.61/0.99  --inst_restr_to_given                   false
% 1.61/0.99  --inst_activity_threshold               500
% 1.61/0.99  --inst_out_proof                        true
% 1.61/0.99  
% 1.61/0.99  ------ Resolution Options
% 1.61/0.99  
% 1.61/0.99  --resolution_flag                       false
% 1.61/0.99  --res_lit_sel                           adaptive
% 1.61/0.99  --res_lit_sel_side                      none
% 1.61/0.99  --res_ordering                          kbo
% 1.61/0.99  --res_to_prop_solver                    active
% 1.61/0.99  --res_prop_simpl_new                    false
% 1.61/0.99  --res_prop_simpl_given                  true
% 1.61/0.99  --res_passive_queue_type                priority_queues
% 1.61/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.61/0.99  --res_passive_queues_freq               [15;5]
% 1.61/0.99  --res_forward_subs                      full
% 1.61/0.99  --res_backward_subs                     full
% 1.61/0.99  --res_forward_subs_resolution           true
% 1.61/0.99  --res_backward_subs_resolution          true
% 1.61/0.99  --res_orphan_elimination                true
% 1.61/0.99  --res_time_limit                        2.
% 1.61/0.99  --res_out_proof                         true
% 1.61/0.99  
% 1.61/0.99  ------ Superposition Options
% 1.61/0.99  
% 1.61/0.99  --superposition_flag                    true
% 1.61/0.99  --sup_passive_queue_type                priority_queues
% 1.61/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.61/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.61/0.99  --demod_completeness_check              fast
% 1.61/0.99  --demod_use_ground                      true
% 1.61/0.99  --sup_to_prop_solver                    passive
% 1.61/0.99  --sup_prop_simpl_new                    true
% 1.61/0.99  --sup_prop_simpl_given                  true
% 1.61/0.99  --sup_fun_splitting                     false
% 1.61/0.99  --sup_smt_interval                      50000
% 1.61/0.99  
% 1.61/0.99  ------ Superposition Simplification Setup
% 1.61/0.99  
% 1.61/0.99  --sup_indices_passive                   []
% 1.61/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.61/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.61/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.99  --sup_full_bw                           [BwDemod]
% 1.61/0.99  --sup_immed_triv                        [TrivRules]
% 1.61/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.61/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.99  --sup_immed_bw_main                     []
% 1.61/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.61/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.61/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.61/0.99  
% 1.61/0.99  ------ Combination Options
% 1.61/0.99  
% 1.61/0.99  --comb_res_mult                         3
% 1.61/0.99  --comb_sup_mult                         2
% 1.61/0.99  --comb_inst_mult                        10
% 1.61/0.99  
% 1.61/0.99  ------ Debug Options
% 1.61/0.99  
% 1.61/0.99  --dbg_backtrace                         false
% 1.61/0.99  --dbg_dump_prop_clauses                 false
% 1.61/0.99  --dbg_dump_prop_clauses_file            -
% 1.61/0.99  --dbg_out_stat                          false
% 1.61/0.99  
% 1.61/0.99  
% 1.61/0.99  
% 1.61/0.99  
% 1.61/0.99  ------ Proving...
% 1.61/0.99  
% 1.61/0.99  
% 1.61/0.99  % SZS status Theorem for theBenchmark.p
% 1.61/0.99  
% 1.61/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.61/0.99  
% 1.61/0.99  fof(f6,conjecture,(
% 1.61/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 1.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.99  
% 1.61/0.99  fof(f7,negated_conjecture,(
% 1.61/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 1.61/0.99    inference(negated_conjecture,[],[f6])).
% 1.61/0.99  
% 1.61/0.99  fof(f17,plain,(
% 1.61/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.61/0.99    inference(ennf_transformation,[],[f7])).
% 1.61/0.99  
% 1.61/0.99  fof(f18,plain,(
% 1.61/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.61/0.99    inference(flattening,[],[f17])).
% 1.61/0.99  
% 1.61/0.99  fof(f24,plain,(
% 1.61/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5) & r1_tarski(sK5,u1_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 1.61/0.99    introduced(choice_axiom,[])).
% 1.61/0.99  
% 1.61/0.99  fof(f23,plain,(
% 1.61/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.61/0.99    introduced(choice_axiom,[])).
% 1.61/0.99  
% 1.61/0.99  fof(f22,plain,(
% 1.61/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.61/0.99    introduced(choice_axiom,[])).
% 1.61/0.99  
% 1.61/0.99  fof(f21,plain,(
% 1.61/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.61/0.99    introduced(choice_axiom,[])).
% 1.61/0.99  
% 1.61/0.99  fof(f20,plain,(
% 1.61/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.61/0.99    introduced(choice_axiom,[])).
% 1.61/0.99  
% 1.61/0.99  fof(f19,plain,(
% 1.61/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.61/0.99    introduced(choice_axiom,[])).
% 1.61/0.99  
% 1.61/0.99  fof(f25,plain,(
% 1.61/0.99    (((((k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f24,f23,f22,f21,f20,f19])).
% 1.61/0.99  
% 1.61/0.99  fof(f38,plain,(
% 1.61/0.99    m1_pre_topc(sK2,sK0)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f4,axiom,(
% 1.61/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 1.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.99  
% 1.61/0.99  fof(f13,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.61/0.99    inference(ennf_transformation,[],[f4])).
% 1.61/0.99  
% 1.61/0.99  fof(f14,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.61/0.99    inference(flattening,[],[f13])).
% 1.61/0.99  
% 1.61/0.99  fof(f29,plain,(
% 1.61/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.61/0.99    inference(cnf_transformation,[],[f14])).
% 1.61/0.99  
% 1.61/0.99  fof(f42,plain,(
% 1.61/0.99    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f41,plain,(
% 1.61/0.99    v1_funct_1(sK4)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f34,plain,(
% 1.61/0.99    ~v2_struct_0(sK1)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f35,plain,(
% 1.61/0.99    v2_pre_topc(sK1)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f36,plain,(
% 1.61/0.99    l1_pre_topc(sK1)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f43,plain,(
% 1.61/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f44,plain,(
% 1.61/0.99    m1_pre_topc(sK2,sK3)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f3,axiom,(
% 1.61/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.99  
% 1.61/0.99  fof(f11,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.61/0.99    inference(ennf_transformation,[],[f3])).
% 1.61/0.99  
% 1.61/0.99  fof(f12,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.61/0.99    inference(flattening,[],[f11])).
% 1.61/0.99  
% 1.61/0.99  fof(f28,plain,(
% 1.61/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.61/0.99    inference(cnf_transformation,[],[f12])).
% 1.61/0.99  
% 1.61/0.99  fof(f32,plain,(
% 1.61/0.99    v2_pre_topc(sK0)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f33,plain,(
% 1.61/0.99    l1_pre_topc(sK0)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f39,plain,(
% 1.61/0.99    ~v2_struct_0(sK3)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f40,plain,(
% 1.61/0.99    m1_pre_topc(sK3,sK0)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f1,axiom,(
% 1.61/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.99  
% 1.61/0.99  fof(f8,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.61/0.99    inference(ennf_transformation,[],[f1])).
% 1.61/0.99  
% 1.61/0.99  fof(f9,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.61/0.99    inference(flattening,[],[f8])).
% 1.61/0.99  
% 1.61/0.99  fof(f26,plain,(
% 1.61/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.61/0.99    inference(cnf_transformation,[],[f9])).
% 1.61/0.99  
% 1.61/0.99  fof(f2,axiom,(
% 1.61/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.99  
% 1.61/0.99  fof(f10,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.99    inference(ennf_transformation,[],[f2])).
% 1.61/0.99  
% 1.61/0.99  fof(f27,plain,(
% 1.61/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.99    inference(cnf_transformation,[],[f10])).
% 1.61/0.99  
% 1.61/0.99  fof(f5,axiom,(
% 1.61/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 1.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.61/0.99  
% 1.61/0.99  fof(f15,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ~r1_tarski(X4,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.61/0.99    inference(ennf_transformation,[],[f5])).
% 1.61/0.99  
% 1.61/0.99  fof(f16,plain,(
% 1.61/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ~r1_tarski(X4,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.61/0.99    inference(flattening,[],[f15])).
% 1.61/0.99  
% 1.61/0.99  fof(f30,plain,(
% 1.61/0.99    ( ! [X4,X2,X0,X3,X1] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ~r1_tarski(X4,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.61/0.99    inference(cnf_transformation,[],[f16])).
% 1.61/0.99  
% 1.61/0.99  fof(f46,plain,(
% 1.61/0.99    r1_tarski(sK5,u1_struct_0(sK2))),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f47,plain,(
% 1.61/0.99    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f45,plain,(
% 1.61/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f37,plain,(
% 1.61/0.99    ~v2_struct_0(sK2)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  fof(f31,plain,(
% 1.61/0.99    ~v2_struct_0(sK0)),
% 1.61/0.99    inference(cnf_transformation,[],[f25])).
% 1.61/0.99  
% 1.61/0.99  cnf(c_14,negated_conjecture,
% 1.61/0.99      ( m1_pre_topc(sK2,sK0) ),
% 1.61/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_548,negated_conjecture,
% 1.61/0.99      ( m1_pre_topc(sK2,sK0) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_862,plain,
% 1.61/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_3,plain,
% 1.61/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.61/0.99      | ~ m1_pre_topc(X3,X4)
% 1.61/0.99      | ~ m1_pre_topc(X3,X1)
% 1.61/0.99      | ~ m1_pre_topc(X1,X4)
% 1.61/0.99      | v2_struct_0(X4)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | ~ v1_funct_1(X0)
% 1.61/0.99      | ~ l1_pre_topc(X4)
% 1.61/0.99      | ~ l1_pre_topc(X2)
% 1.61/0.99      | ~ v2_pre_topc(X4)
% 1.61/0.99      | ~ v2_pre_topc(X2)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 1.61/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_10,negated_conjecture,
% 1.61/0.99      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 1.61/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_316,plain,
% 1.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.61/0.99      | ~ m1_pre_topc(X3,X1)
% 1.61/0.99      | ~ m1_pre_topc(X3,X4)
% 1.61/0.99      | ~ m1_pre_topc(X1,X4)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | v2_struct_0(X4)
% 1.61/0.99      | ~ v1_funct_1(X0)
% 1.61/0.99      | ~ l1_pre_topc(X2)
% 1.61/0.99      | ~ l1_pre_topc(X4)
% 1.61/0.99      | ~ v2_pre_topc(X2)
% 1.61/0.99      | ~ v2_pre_topc(X4)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0)
% 1.61/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.61/0.99      | sK4 != X0 ),
% 1.61/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_317,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | ~ m1_pre_topc(X2,X3)
% 1.61/0.99      | ~ m1_pre_topc(X0,X3)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X3)
% 1.61/0.99      | ~ v1_funct_1(sK4)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X3)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(unflattening,[status(thm)],[c_316]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_11,negated_conjecture,
% 1.61/0.99      ( v1_funct_1(sK4) ),
% 1.61/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_321,plain,
% 1.61/0.99      ( v2_struct_0(X3)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | ~ m1_pre_topc(X0,X3)
% 1.61/0.99      | ~ m1_pre_topc(X2,X3)
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X3)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(global_propositional_subsumption,
% 1.61/0.99                [status(thm)],
% 1.61/0.99                [c_317,c_11]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_322,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | ~ m1_pre_topc(X2,X3)
% 1.61/0.99      | ~ m1_pre_topc(X0,X3)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X3)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X3)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK4)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(renaming,[status(thm)],[c_321]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_539,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 1.61/0.99      | ~ m1_pre_topc(X2_52,X0_52)
% 1.61/0.99      | ~ m1_pre_topc(X2_52,X3_52)
% 1.61/0.99      | ~ m1_pre_topc(X0_52,X3_52)
% 1.61/0.99      | v2_struct_0(X1_52)
% 1.61/0.99      | v2_struct_0(X3_52)
% 1.61/0.99      | ~ l1_pre_topc(X1_52)
% 1.61/0.99      | ~ l1_pre_topc(X3_52)
% 1.61/0.99      | ~ v2_pre_topc(X1_52)
% 1.61/0.99      | ~ v2_pre_topc(X3_52)
% 1.61/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,sK4) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_322]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_871,plain,
% 1.61/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X0_52,X1_52,X2_52,sK4)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X2_52,X1_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X3_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.61/0.99      | v2_struct_0(X3_52) = iProver_top
% 1.61/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | l1_pre_topc(X3_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X3_52) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1431,plain,
% 1.61/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK4)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X2_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X2_52) = iProver_top
% 1.61/0.99      | v2_struct_0(sK1) = iProver_top
% 1.61/0.99      | l1_pre_topc(X2_52) != iProver_top
% 1.61/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.61/0.99      | v2_pre_topc(X2_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 1.61/0.99      inference(equality_resolution,[status(thm)],[c_871]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_18,negated_conjecture,
% 1.61/0.99      ( ~ v2_struct_0(sK1) ),
% 1.61/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_25,plain,
% 1.61/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_17,negated_conjecture,
% 1.61/0.99      ( v2_pre_topc(sK1) ),
% 1.61/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_26,plain,
% 1.61/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_16,negated_conjecture,
% 1.61/0.99      ( l1_pre_topc(sK1) ),
% 1.61/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_27,plain,
% 1.61/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_560,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1036,plain,
% 1.61/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_560]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1037,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
% 1.61/0.99      | ~ m1_pre_topc(X0_52,X1_52)
% 1.61/0.99      | ~ m1_pre_topc(X2_52,X0_52)
% 1.61/0.99      | ~ m1_pre_topc(X2_52,X1_52)
% 1.61/0.99      | v2_struct_0(X1_52)
% 1.61/0.99      | v2_struct_0(sK1)
% 1.61/0.99      | ~ l1_pre_topc(X1_52)
% 1.61/0.99      | ~ l1_pre_topc(sK1)
% 1.61/0.99      | ~ v2_pre_topc(X1_52)
% 1.61/0.99      | ~ v2_pre_topc(sK1)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X2_52)) = k3_tmap_1(X1_52,sK1,X0_52,X2_52,sK4) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_539]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1041,plain,
% 1.61/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK4)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X2_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X2_52) = iProver_top
% 1.61/0.99      | v2_struct_0(sK1) = iProver_top
% 1.61/0.99      | l1_pre_topc(X2_52) != iProver_top
% 1.61/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.61/0.99      | v2_pre_topc(X2_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1611,plain,
% 1.61/0.99      ( v2_pre_topc(X2_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X2_52) = iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X2_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK4)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | l1_pre_topc(X2_52) != iProver_top ),
% 1.61/0.99      inference(global_propositional_subsumption,
% 1.61/0.99                [status(thm)],
% 1.61/0.99                [c_1431,c_25,c_26,c_27,c_1036,c_1041]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1612,plain,
% 1.61/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k3_tmap_1(X2_52,sK1,X0_52,X1_52,sK4)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X2_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X2_52) = iProver_top
% 1.61/0.99      | l1_pre_topc(X2_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X2_52) != iProver_top ),
% 1.61/0.99      inference(renaming,[status(thm)],[c_1611]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1624,plain,
% 1.61/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK3,X0_52,sK4)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X0_52,sK3) != iProver_top
% 1.61/0.99      | m1_pre_topc(sK3,X1_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X1_52) = iProver_top
% 1.61/0.99      | l1_pre_topc(X1_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X1_52) != iProver_top ),
% 1.61/0.99      inference(equality_resolution,[status(thm)],[c_1612]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_9,negated_conjecture,
% 1.61/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 1.61/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_34,plain,
% 1.61/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1774,plain,
% 1.61/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK3,X0_52,sK4)
% 1.61/0.99      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 1.61/0.99      | m1_pre_topc(X0_52,sK3) != iProver_top
% 1.61/0.99      | m1_pre_topc(sK3,X1_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X1_52) = iProver_top
% 1.61/0.99      | l1_pre_topc(X1_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X1_52) != iProver_top ),
% 1.61/0.99      inference(global_propositional_subsumption,
% 1.61/0.99                [status(thm)],
% 1.61/0.99                [c_1624,c_34]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1789,plain,
% 1.61/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,sK4)
% 1.61/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.61/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 1.61/0.99      | v2_struct_0(sK0) = iProver_top
% 1.61/0.99      | l1_pre_topc(sK0) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 1.61/0.99      inference(superposition,[status(thm)],[c_862,c_1774]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_8,negated_conjecture,
% 1.61/0.99      ( m1_pre_topc(sK2,sK3) ),
% 1.61/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_552,negated_conjecture,
% 1.61/0.99      ( m1_pre_topc(sK2,sK3) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_858,plain,
% 1.61/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_2,plain,
% 1.61/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.61/0.99      | ~ m1_pre_topc(X3,X1)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | ~ v1_funct_1(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X2)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X2)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 1.61/0.99      inference(cnf_transformation,[],[f28]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_367,plain,
% 1.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.61/0.99      | ~ m1_pre_topc(X3,X1)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | ~ v1_funct_1(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X2)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X2)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 1.61/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.61/0.99      | sK4 != X0 ),
% 1.61/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_368,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | v2_struct_0(X0)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | ~ v1_funct_1(sK4)
% 1.61/0.99      | ~ l1_pre_topc(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X0)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(unflattening,[status(thm)],[c_367]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_372,plain,
% 1.61/0.99      ( v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X0)
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ l1_pre_topc(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X0)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(global_propositional_subsumption,
% 1.61/0.99                [status(thm)],
% 1.61/0.99                [c_368,c_11]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_373,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X0)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X0)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK4,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK4,X2)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(renaming,[status(thm)],[c_372]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_538,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 1.61/0.99      | ~ m1_pre_topc(X2_52,X0_52)
% 1.61/0.99      | v2_struct_0(X1_52)
% 1.61/0.99      | v2_struct_0(X0_52)
% 1.61/0.99      | ~ l1_pre_topc(X1_52)
% 1.61/0.99      | ~ l1_pre_topc(X0_52)
% 1.61/0.99      | ~ v2_pre_topc(X1_52)
% 1.61/0.99      | ~ v2_pre_topc(X0_52)
% 1.61/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,sK4,X2_52) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_373]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_872,plain,
% 1.61/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,u1_struct_0(X2_52)) = k2_tmap_1(X1_52,X0_52,sK4,X2_52)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X2_52,X1_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.61/0.99      | v2_struct_0(X1_52) = iProver_top
% 1.61/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | l1_pre_topc(X1_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X1_52) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1365,plain,
% 1.61/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.61/0.99      | v2_struct_0(sK1) = iProver_top
% 1.61/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.61/0.99      | v2_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 1.61/0.99      inference(equality_resolution,[status(thm)],[c_872]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1038,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
% 1.61/0.99      | ~ m1_pre_topc(X1_52,X0_52)
% 1.61/0.99      | v2_struct_0(X0_52)
% 1.61/0.99      | v2_struct_0(sK1)
% 1.61/0.99      | ~ l1_pre_topc(X0_52)
% 1.61/0.99      | ~ l1_pre_topc(sK1)
% 1.61/0.99      | ~ v2_pre_topc(X0_52)
% 1.61/0.99      | ~ v2_pre_topc(sK1)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_538]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1039,plain,
% 1.61/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.61/0.99      | v2_struct_0(sK1) = iProver_top
% 1.61/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.61/0.99      | v2_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK1) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1038]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1549,plain,
% 1.61/0.99      ( v2_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | l1_pre_topc(X0_52) != iProver_top ),
% 1.61/0.99      inference(global_propositional_subsumption,
% 1.61/0.99                [status(thm)],
% 1.61/0.99                [c_1365,c_25,c_26,c_27,c_1036,c_1039]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1550,plain,
% 1.61/0.99      ( u1_struct_0(X0_52) != u1_struct_0(sK3)
% 1.61/0.99      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(sK1),sK4,u1_struct_0(X1_52)) = k2_tmap_1(X0_52,sK1,sK4,X1_52)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 1.61/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.61/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X0_52) != iProver_top ),
% 1.61/0.99      inference(renaming,[status(thm)],[c_1549]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1560,plain,
% 1.61/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK1,sK4,X0_52)
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(X0_52,sK3) != iProver_top
% 1.61/0.99      | v2_struct_0(sK3) = iProver_top
% 1.61/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 1.61/0.99      inference(equality_resolution,[status(thm)],[c_1550]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_20,negated_conjecture,
% 1.61/0.99      ( v2_pre_topc(sK0) ),
% 1.61/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_23,plain,
% 1.61/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_19,negated_conjecture,
% 1.61/0.99      ( l1_pre_topc(sK0) ),
% 1.61/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_24,plain,
% 1.61/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_13,negated_conjecture,
% 1.61/0.99      ( ~ v2_struct_0(sK3) ),
% 1.61/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_30,plain,
% 1.61/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_12,negated_conjecture,
% 1.61/0.99      ( m1_pre_topc(sK3,sK0) ),
% 1.61/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_31,plain,
% 1.61/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_550,negated_conjecture,
% 1.61/0.99      ( m1_pre_topc(sK3,sK0) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_860,plain,
% 1.61/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_0,plain,
% 1.61/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | v2_pre_topc(X0) ),
% 1.61/0.99      inference(cnf_transformation,[],[f26]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_556,plain,
% 1.61/0.99      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.61/0.99      | ~ l1_pre_topc(X1_52)
% 1.61/0.99      | ~ v2_pre_topc(X1_52)
% 1.61/0.99      | v2_pre_topc(X0_52) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_855,plain,
% 1.61/0.99      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 1.61/0.99      | l1_pre_topc(X1_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X1_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(X0_52) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1132,plain,
% 1.61/0.99      ( l1_pre_topc(sK0) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK0) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK3) = iProver_top ),
% 1.61/0.99      inference(superposition,[status(thm)],[c_860,c_855]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1,plain,
% 1.61/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.61/0.99      inference(cnf_transformation,[],[f27]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_555,plain,
% 1.61/0.99      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.61/0.99      | ~ l1_pre_topc(X1_52)
% 1.61/0.99      | l1_pre_topc(X0_52) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1093,plain,
% 1.61/0.99      ( ~ m1_pre_topc(sK3,X0_52)
% 1.61/0.99      | ~ l1_pre_topc(X0_52)
% 1.61/0.99      | l1_pre_topc(sK3) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_555]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1191,plain,
% 1.61/0.99      ( ~ m1_pre_topc(sK3,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_1093]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1192,plain,
% 1.61/0.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 1.61/0.99      | l1_pre_topc(sK0) != iProver_top
% 1.61/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1191]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1692,plain,
% 1.61/0.99      ( m1_pre_topc(X0_52,sK3) != iProver_top
% 1.61/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK1,sK4,X0_52) ),
% 1.61/0.99      inference(global_propositional_subsumption,
% 1.61/0.99                [status(thm)],
% 1.61/0.99                [c_1560,c_23,c_24,c_30,c_31,c_34,c_1132,c_1192]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1693,plain,
% 1.61/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK3,sK1,sK4,X0_52)
% 1.61/0.99      | m1_pre_topc(X0_52,sK3) != iProver_top ),
% 1.61/0.99      inference(renaming,[status(thm)],[c_1692]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1700,plain,
% 1.61/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) ),
% 1.61/0.99      inference(superposition,[status(thm)],[c_858,c_1693]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1796,plain,
% 1.61/0.99      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK3,sK1,sK4,sK2)
% 1.61/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.61/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 1.61/0.99      | v2_struct_0(sK0) = iProver_top
% 1.61/0.99      | l1_pre_topc(sK0) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 1.61/0.99      inference(light_normalisation,[status(thm)],[c_1789,c_1700]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_571,plain,
% 1.61/0.99      ( k7_relset_1(X0_51,X1_51,X0_49,X1_49) = k7_relset_1(X2_51,X3_51,X2_49,X3_49)
% 1.61/0.99      | X0_51 != X2_51
% 1.61/0.99      | X1_51 != X3_51
% 1.61/0.99      | X0_49 != X2_49
% 1.61/0.99      | X1_49 != X3_49 ),
% 1.61/0.99      theory(equality) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1659,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
% 1.61/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.61/0.99      | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) != k2_tmap_1(sK3,sK1,sK4,sK2)
% 1.61/0.99      | sK5 != sK5 ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_571]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_564,plain,
% 1.61/0.99      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 1.61/0.99      theory(equality) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1121,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != X0_53
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X0_53 ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_564]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1575,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_1121]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1069,plain,
% 1.61/0.99      ( X0_53 != X1_53
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X1_53
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_53 ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_564]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1204,plain,
% 1.61/0.99      ( X0_53 != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = X0_53
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_1069]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1331,plain,
% 1.61/0.99      ( k7_relset_1(X0_51,X1_51,X0_49,X1_49) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(X0_51,X1_51,X0_49,X1_49)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_1204]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1528,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_1331]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1308,plain,
% 1.61/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_560]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_4,plain,
% 1.61/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.61/0.99      | ~ r1_tarski(X3,u1_struct_0(X4))
% 1.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.61/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.61/0.99      | ~ m1_pre_topc(X4,X1)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X4)
% 1.61/0.99      | ~ v1_funct_1(X0)
% 1.61/0.99      | ~ l1_pre_topc(X2)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X2)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,X4),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) ),
% 1.61/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_6,negated_conjecture,
% 1.61/0.99      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 1.61/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_213,plain,
% 1.61/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.61/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.61/0.99      | ~ m1_pre_topc(X4,X1)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | v2_struct_0(X4)
% 1.61/0.99      | ~ v1_funct_1(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X2)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X2)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,X4),X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3)
% 1.61/0.99      | u1_struct_0(X4) != u1_struct_0(sK2)
% 1.61/0.99      | sK5 != X3 ),
% 1.61/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_6]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_214,plain,
% 1.61/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.61/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
% 1.61/0.99      | ~ m1_pre_topc(X3,X1)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | v2_struct_0(X3)
% 1.61/0.99      | ~ v1_funct_1(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X2)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X2)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,X3),sK5) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK5)
% 1.61/0.99      | u1_struct_0(X3) != u1_struct_0(sK2) ),
% 1.61/0.99      inference(unflattening,[status(thm)],[c_213]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_262,plain,
% 1.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.61/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1)))
% 1.61/0.99      | ~ m1_pre_topc(X3,X1)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | v2_struct_0(X3)
% 1.61/0.99      | ~ v1_funct_1(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X2)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X2)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,X3),sK5) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK5)
% 1.61/0.99      | u1_struct_0(X3) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK3)
% 1.61/0.99      | sK4 != X0 ),
% 1.61/0.99      inference(resolution_lifted,[status(thm)],[c_214,c_10]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_263,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.61/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | v2_struct_0(X0)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | ~ v1_funct_1(sK4)
% 1.61/0.99      | ~ l1_pre_topc(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X0)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),sK5) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK5)
% 1.61/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(unflattening,[status(thm)],[c_262]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_267,plain,
% 1.61/0.99      ( v2_struct_0(X2)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X0)
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.61/0.99      | ~ l1_pre_topc(X0)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X0)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),sK5) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK5)
% 1.61/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(global_propositional_subsumption,
% 1.61/0.99                [status(thm)],
% 1.61/0.99                [c_263,c_11]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_268,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.61/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.61/0.99      | ~ m1_pre_topc(X2,X0)
% 1.61/0.99      | v2_struct_0(X1)
% 1.61/0.99      | v2_struct_0(X0)
% 1.61/0.99      | v2_struct_0(X2)
% 1.61/0.99      | ~ l1_pre_topc(X1)
% 1.61/0.99      | ~ l1_pre_topc(X0)
% 1.61/0.99      | ~ v2_pre_topc(X1)
% 1.61/0.99      | ~ v2_pre_topc(X0)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),sK5) = k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK5)
% 1.61/0.99      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(renaming,[status(thm)],[c_267]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_540,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_52)))
% 1.61/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 1.61/0.99      | ~ m1_pre_topc(X2_52,X0_52)
% 1.61/0.99      | v2_struct_0(X1_52)
% 1.61/0.99      | v2_struct_0(X0_52)
% 1.61/0.99      | v2_struct_0(X2_52)
% 1.61/0.99      | ~ l1_pre_topc(X1_52)
% 1.61/0.99      | ~ l1_pre_topc(X0_52)
% 1.61/0.99      | ~ v2_pre_topc(X1_52)
% 1.61/0.99      | ~ v2_pre_topc(X0_52)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X2_52),u1_struct_0(X1_52),k2_tmap_1(X0_52,X1_52,sK4,X2_52),sK5) = k7_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,sK5)
% 1.61/0.99      | u1_struct_0(X2_52) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_268]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1031,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.61/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
% 1.61/0.99      | ~ m1_pre_topc(X1_52,sK3)
% 1.61/0.99      | v2_struct_0(X1_52)
% 1.61/0.99      | v2_struct_0(X0_52)
% 1.61/0.99      | v2_struct_0(sK3)
% 1.61/0.99      | ~ l1_pre_topc(X0_52)
% 1.61/0.99      | ~ l1_pre_topc(sK3)
% 1.61/0.99      | ~ v2_pre_topc(X0_52)
% 1.61/0.99      | ~ v2_pre_topc(sK3)
% 1.61/0.99      | k7_relset_1(u1_struct_0(X1_52),u1_struct_0(X0_52),k2_tmap_1(sK3,X0_52,sK4,X1_52),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0_52),sK4,sK5)
% 1.61/0.99      | u1_struct_0(X1_52) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_540]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1283,plain,
% 1.61/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.61/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52))))
% 1.61/0.99      | ~ m1_pre_topc(sK2,sK3)
% 1.61/0.99      | v2_struct_0(X0_52)
% 1.61/0.99      | v2_struct_0(sK2)
% 1.61/0.99      | v2_struct_0(sK3)
% 1.61/0.99      | ~ l1_pre_topc(X0_52)
% 1.61/0.99      | ~ l1_pre_topc(sK3)
% 1.61/0.99      | ~ v2_pre_topc(X0_52)
% 1.61/0.99      | ~ v2_pre_topc(sK3)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_52),k2_tmap_1(sK3,X0_52,sK4,sK2),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0_52),sK4,sK5)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_1031]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1284,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0_52),k2_tmap_1(sK3,X0_52,sK4,sK2),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(X0_52),sK4,sK5)
% 1.61/0.99      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.61/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.61/0.99      | v2_struct_0(X0_52) = iProver_top
% 1.61/0.99      | v2_struct_0(sK2) = iProver_top
% 1.61/0.99      | v2_struct_0(sK3) = iProver_top
% 1.61/0.99      | l1_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.61/0.99      | v2_pre_topc(X0_52) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1283]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1286,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,sK4,sK2),sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.61/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.61/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.61/0.99      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 1.61/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.61/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 1.61/0.99      | m1_pre_topc(sK2,sK3) != iProver_top
% 1.61/0.99      | v2_struct_0(sK2) = iProver_top
% 1.61/0.99      | v2_struct_0(sK1) = iProver_top
% 1.61/0.99      | v2_struct_0(sK3) = iProver_top
% 1.61/0.99      | l1_pre_topc(sK1) != iProver_top
% 1.61/0.99      | l1_pre_topc(sK3) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK1) != iProver_top
% 1.61/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_1284]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1105,plain,
% 1.61/0.99      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_560]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_558,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1075,plain,
% 1.61/0.99      ( sK5 = sK5 ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_558]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_561,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1068,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_561]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1048,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != X0_53
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != X0_53
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_564]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_1067,plain,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 1.61/0.99      | k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 1.61/0.99      inference(instantiation,[status(thm)],[c_1048]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_5,negated_conjecture,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 1.61/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_554,negated_conjecture,
% 1.61/0.99      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 1.61/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_7,negated_conjecture,
% 1.61/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.61/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_36,plain,
% 1.61/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_35,plain,
% 1.61/0.99      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_15,negated_conjecture,
% 1.61/0.99      ( ~ v2_struct_0(sK2) ),
% 1.61/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_28,plain,
% 1.61/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_21,negated_conjecture,
% 1.61/0.99      ( ~ v2_struct_0(sK0) ),
% 1.61/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(c_22,plain,
% 1.61/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 1.61/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.61/0.99  
% 1.61/0.99  cnf(contradiction,plain,
% 1.61/0.99      ( $false ),
% 1.61/0.99      inference(minisat,
% 1.61/0.99                [status(thm)],
% 1.61/0.99                [c_1796,c_1659,c_1575,c_1528,c_1308,c_1286,c_1192,c_1132,
% 1.61/0.99                 c_1105,c_1075,c_1068,c_1067,c_1036,c_554,c_36,c_35,c_34,
% 1.61/0.99                 c_31,c_30,c_28,c_27,c_26,c_25,c_24,c_23,c_22]) ).
% 1.61/0.99  
% 1.61/0.99  
% 1.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.61/0.99  
% 1.61/0.99  ------                               Statistics
% 1.61/0.99  
% 1.61/0.99  ------ General
% 1.61/0.99  
% 1.61/0.99  abstr_ref_over_cycles:                  0
% 1.61/0.99  abstr_ref_under_cycles:                 0
% 1.61/0.99  gc_basic_clause_elim:                   0
% 1.61/0.99  forced_gc_time:                         0
% 1.61/0.99  parsing_time:                           0.01
% 1.61/0.99  unif_index_cands_time:                  0.
% 1.61/0.99  unif_index_add_time:                    0.
% 1.61/0.99  orderings_time:                         0.
% 1.61/0.99  out_proof_time:                         0.012
% 1.61/0.99  total_time:                             0.11
% 1.61/0.99  num_of_symbols:                         57
% 1.61/0.99  num_of_terms:                           1572
% 1.61/0.99  
% 1.61/0.99  ------ Preprocessing
% 1.61/0.99  
% 1.61/0.99  num_of_splits:                          0
% 1.61/0.99  num_of_split_atoms:                     0
% 1.61/0.99  num_of_reused_defs:                     0
% 1.61/0.99  num_eq_ax_congr_red:                    21
% 1.61/0.99  num_of_sem_filtered_clauses:            1
% 1.61/0.99  num_of_subtypes:                        5
% 1.61/0.99  monotx_restored_types:                  0
% 1.61/0.99  sat_num_of_epr_types:                   0
% 1.61/0.99  sat_num_of_non_cyclic_types:            0
% 1.61/0.99  sat_guarded_non_collapsed_types:        0
% 1.61/0.99  num_pure_diseq_elim:                    0
% 1.61/0.99  simp_replaced_by:                       0
% 1.61/0.99  res_preprocessed:                       108
% 1.61/0.99  prep_upred:                             0
% 1.61/0.99  prep_unflattend:                        4
% 1.61/0.99  smt_new_axioms:                         0
% 1.61/0.99  pred_elim_cands:                        5
% 1.61/0.99  pred_elim:                              3
% 1.61/0.99  pred_elim_cl:                           3
% 1.61/0.99  pred_elim_cycles:                       5
% 1.61/0.99  merged_defs:                            0
% 1.61/0.99  merged_defs_ncl:                        0
% 1.61/0.99  bin_hyper_res:                          0
% 1.61/0.99  prep_cycles:                            4
% 1.61/0.99  pred_elim_time:                         0.008
% 1.61/0.99  splitting_time:                         0.
% 1.61/0.99  sem_filter_time:                        0.
% 1.61/0.99  monotx_time:                            0.
% 1.61/0.99  subtype_inf_time:                       0.
% 1.61/0.99  
% 1.61/0.99  ------ Problem properties
% 1.61/0.99  
% 1.61/0.99  clauses:                                19
% 1.61/0.99  conjectures:                            14
% 1.61/0.99  epr:                                    13
% 1.61/0.99  horn:                                   16
% 1.61/0.99  ground:                                 14
% 1.61/0.99  unary:                                  14
% 1.61/0.99  binary:                                 0
% 1.61/0.99  lits:                                   59
% 1.61/0.99  lits_eq:                                11
% 1.61/0.99  fd_pure:                                0
% 1.61/0.99  fd_pseudo:                              0
% 1.61/0.99  fd_cond:                                0
% 1.61/0.99  fd_pseudo_cond:                         0
% 1.61/0.99  ac_symbols:                             0
% 1.61/0.99  
% 1.61/0.99  ------ Propositional Solver
% 1.61/0.99  
% 1.61/0.99  prop_solver_calls:                      29
% 1.61/0.99  prop_fast_solver_calls:                 882
% 1.61/0.99  smt_solver_calls:                       0
% 1.61/0.99  smt_fast_solver_calls:                  0
% 1.61/0.99  prop_num_of_clauses:                    416
% 1.61/0.99  prop_preprocess_simplified:             2425
% 1.61/0.99  prop_fo_subsumed:                       26
% 1.61/0.99  prop_solver_time:                       0.
% 1.61/0.99  smt_solver_time:                        0.
% 1.61/0.99  smt_fast_solver_time:                   0.
% 1.61/0.99  prop_fast_solver_time:                  0.
% 1.61/0.99  prop_unsat_core_time:                   0.
% 1.61/0.99  
% 1.61/0.99  ------ QBF
% 1.61/0.99  
% 1.61/0.99  qbf_q_res:                              0
% 1.61/0.99  qbf_num_tautologies:                    0
% 1.61/0.99  qbf_prep_cycles:                        0
% 1.61/0.99  
% 1.61/0.99  ------ BMC1
% 1.61/0.99  
% 1.61/0.99  bmc1_current_bound:                     -1
% 1.61/0.99  bmc1_last_solved_bound:                 -1
% 1.61/0.99  bmc1_unsat_core_size:                   -1
% 1.61/0.99  bmc1_unsat_core_parents_size:           -1
% 1.61/0.99  bmc1_merge_next_fun:                    0
% 1.61/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.61/0.99  
% 1.61/0.99  ------ Instantiation
% 1.61/0.99  
% 1.61/0.99  inst_num_of_clauses:                    167
% 1.61/0.99  inst_num_in_passive:                    5
% 1.61/0.99  inst_num_in_active:                     136
% 1.61/0.99  inst_num_in_unprocessed:                26
% 1.61/0.99  inst_num_of_loops:                      150
% 1.61/0.99  inst_num_of_learning_restarts:          0
% 1.61/0.99  inst_num_moves_active_passive:          8
% 1.61/0.99  inst_lit_activity:                      0
% 1.61/0.99  inst_lit_activity_moves:                0
% 1.61/0.99  inst_num_tautologies:                   0
% 1.61/0.99  inst_num_prop_implied:                  0
% 1.61/0.99  inst_num_existing_simplified:           0
% 1.61/0.99  inst_num_eq_res_simplified:             0
% 1.61/0.99  inst_num_child_elim:                    0
% 1.61/0.99  inst_num_of_dismatching_blockings:      16
% 1.61/0.99  inst_num_of_non_proper_insts:           159
% 1.61/0.99  inst_num_of_duplicates:                 0
% 1.61/0.99  inst_inst_num_from_inst_to_res:         0
% 1.61/0.99  inst_dismatching_checking_time:         0.
% 1.61/0.99  
% 1.61/0.99  ------ Resolution
% 1.61/0.99  
% 1.61/0.99  res_num_of_clauses:                     0
% 1.61/0.99  res_num_in_passive:                     0
% 1.61/0.99  res_num_in_active:                      0
% 1.61/0.99  res_num_of_loops:                       112
% 1.61/0.99  res_forward_subset_subsumed:            42
% 1.61/0.99  res_backward_subset_subsumed:           2
% 1.61/0.99  res_forward_subsumed:                   0
% 1.61/0.99  res_backward_subsumed:                  0
% 1.61/0.99  res_forward_subsumption_resolution:     0
% 1.61/0.99  res_backward_subsumption_resolution:    0
% 1.61/0.99  res_clause_to_clause_subsumption:       110
% 1.61/0.99  res_orphan_elimination:                 0
% 1.61/0.99  res_tautology_del:                      34
% 1.61/0.99  res_num_eq_res_simplified:              0
% 1.61/0.99  res_num_sel_changes:                    0
% 1.61/0.99  res_moves_from_active_to_pass:          0
% 1.61/0.99  
% 1.61/0.99  ------ Superposition
% 1.61/0.99  
% 1.61/0.99  sup_time_total:                         0.
% 1.61/0.99  sup_time_generating:                    0.
% 1.61/0.99  sup_time_sim_full:                      0.
% 1.61/0.99  sup_time_sim_immed:                     0.
% 1.61/0.99  
% 1.61/0.99  sup_num_of_clauses:                     32
% 1.61/0.99  sup_num_in_active:                      29
% 1.61/0.99  sup_num_in_passive:                     3
% 1.61/0.99  sup_num_of_loops:                       28
% 1.61/0.99  sup_fw_superposition:                   9
% 1.61/0.99  sup_bw_superposition:                   1
% 1.61/0.99  sup_immediate_simplified:               2
% 1.61/0.99  sup_given_eliminated:                   0
% 1.61/0.99  comparisons_done:                       0
% 1.61/0.99  comparisons_avoided:                    0
% 1.61/0.99  
% 1.61/0.99  ------ Simplifications
% 1.61/0.99  
% 1.61/0.99  
% 1.61/0.99  sim_fw_subset_subsumed:                 0
% 1.61/0.99  sim_bw_subset_subsumed:                 0
% 1.61/0.99  sim_fw_subsumed:                        0
% 1.61/0.99  sim_bw_subsumed:                        0
% 1.61/0.99  sim_fw_subsumption_res:                 0
% 1.61/0.99  sim_bw_subsumption_res:                 0
% 1.61/0.99  sim_tautology_del:                      0
% 1.61/0.99  sim_eq_tautology_del:                   0
% 1.61/0.99  sim_eq_res_simp:                        0
% 1.61/0.99  sim_fw_demodulated:                     0
% 1.61/0.99  sim_bw_demodulated:                     0
% 1.61/0.99  sim_light_normalised:                   2
% 1.61/0.99  sim_joinable_taut:                      0
% 1.61/0.99  sim_joinable_simp:                      0
% 1.61/0.99  sim_ac_normalised:                      0
% 1.61/0.99  sim_smt_subsumption:                    0
% 1.61/0.99  
%------------------------------------------------------------------------------
