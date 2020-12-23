%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:57 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 435 expanded)
%              Number of clauses        :  105 ( 130 expanded)
%              Number of leaves         :   20 ( 163 expanded)
%              Depth                    :   24
%              Number of atoms          :  685 (4883 expanded)
%              Number of equality atoms :  215 ( 575 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ( r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                             => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
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
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ( r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                               => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5),u1_struct_0(X2))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
              & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5)
            & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5),u1_struct_0(X2))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                  & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_pre_topc(X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5)
                & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                      & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
                    ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5)
                    & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(sK2))
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
                        ( k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5)
                        & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
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

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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
                          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5)
                          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
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

fof(f42,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f34,f41,f40,f39,f38,f37,f36])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f73,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1200,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1758,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1207,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | v5_relat_1(X0_55,X1_57) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1752,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v5_relat_1(X0_55,X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_2471,plain,
    ( v5_relat_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_1752])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(k7_relat_1(X0,X2),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1210,plain,
    ( ~ v5_relat_1(X0_55,X0_57)
    | v5_relat_1(k7_relat_1(X0_55,X1_57),X0_57)
    | ~ v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1749,plain,
    ( v5_relat_1(X0_55,X0_57) != iProver_top
    | v5_relat_1(k7_relat_1(X0_55,X1_57),X0_57) = iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1210])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1212,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_55,X0_57)),X0_57)
    | ~ v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1747,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_55,X0_57)),X0_57) = iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1212])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1214,plain,
    ( ~ v5_relat_1(X0_55,X0_57)
    | r1_tarski(k2_relat_1(X0_55),X0_57)
    | ~ v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1745,plain,
    ( v5_relat_1(X0_55,X0_57) != iProver_top
    | r1_tarski(k2_relat_1(X0_55),X0_57) = iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1214])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1205,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ r1_tarski(k1_relat_1(X0_55),X0_57)
    | ~ r1_tarski(k2_relat_1(X0_55),X1_57)
    | ~ v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1754,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) = iProver_top
    | r1_tarski(k1_relat_1(X0_55),X0_57) != iProver_top
    | r1_tarski(k2_relat_1(X0_55),X1_57) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1205])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1206,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1753,plain,
    ( k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1206])).

cnf(c_3373,plain,
    ( k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55)
    | r1_tarski(k1_relat_1(X0_55),X0_57) != iProver_top
    | r1_tarski(k2_relat_1(X0_55),X1_57) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_1753])).

cnf(c_4047,plain,
    ( k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55)
    | v5_relat_1(X0_55,X1_57) != iProver_top
    | r1_tarski(k1_relat_1(X0_55),X0_57) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_3373])).

cnf(c_4176,plain,
    ( k8_relset_1(X0_57,X1_57,k7_relat_1(X0_55,X0_57),X1_55) = k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55)
    | v5_relat_1(k7_relat_1(X0_55,X0_57),X1_57) != iProver_top
    | v1_relat_1(X0_55) != iProver_top
    | v1_relat_1(k7_relat_1(X0_55,X0_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_4047])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1213,plain,
    ( ~ v1_relat_1(X0_55)
    | v1_relat_1(k7_relat_1(X0_55,X0_57)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1264,plain,
    ( v1_relat_1(X0_55) != iProver_top
    | v1_relat_1(k7_relat_1(X0_55,X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1213])).

cnf(c_4606,plain,
    ( v1_relat_1(X0_55) != iProver_top
    | v5_relat_1(k7_relat_1(X0_55,X0_57),X1_57) != iProver_top
    | k8_relset_1(X0_57,X1_57,k7_relat_1(X0_55,X0_57),X1_55) = k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4176,c_1264])).

cnf(c_4607,plain,
    ( k8_relset_1(X0_57,X1_57,k7_relat_1(X0_55,X0_57),X1_55) = k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55)
    | v5_relat_1(k7_relat_1(X0_55,X0_57),X1_57) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_4606])).

cnf(c_4615,plain,
    ( k8_relset_1(X0_57,X1_57,k7_relat_1(X0_55,X0_57),X1_55) = k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55)
    | v5_relat_1(X0_55,X1_57) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_4607])).

cnf(c_4731,plain,
    ( k8_relset_1(X0_57,u1_struct_0(sK1),k7_relat_1(sK4,X0_57),X0_55) = k10_relat_1(k7_relat_1(sK4,X0_57),X0_55)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_4615])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1208,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1751,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_2466,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_1751])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1211,plain,
    ( ~ v1_relat_1(X0_55)
    | k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55) = k3_xboole_0(X0_57,k10_relat_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1748,plain,
    ( k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55) = k3_xboole_0(X0_57,k10_relat_1(X0_55,X1_55))
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1211])).

cnf(c_2896,plain,
    ( k10_relat_1(k7_relat_1(sK4,X0_57),X0_55) = k3_xboole_0(X0_57,k10_relat_1(sK4,X0_55)) ),
    inference(superposition,[status(thm)],[c_2466,c_1748])).

cnf(c_4734,plain,
    ( k8_relset_1(X0_57,u1_struct_0(sK1),k7_relat_1(sK4,X0_57),X0_55) = k3_xboole_0(X0_57,k10_relat_1(sK4,X0_55))
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4731,c_2896])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1962,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_1963,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1962])).

cnf(c_5236,plain,
    ( k8_relset_1(X0_57,u1_struct_0(sK1),k7_relat_1(sK4,X0_57),X0_55) = k3_xboole_0(X0_57,k10_relat_1(sK4,X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4734,c_44,c_1963])).

cnf(c_2956,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_55) = k10_relat_1(sK4,X0_55) ),
    inference(superposition,[status(thm)],[c_1758,c_1753])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1197,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1761,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1197])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_330,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X4) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_331,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_335,plain,
    ( ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_21])).

cnf(c_336,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
    | u1_struct_0(X3) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_335])).

cnf(c_1189,plain,
    ( ~ m1_pre_topc(X0_58,X1_58)
    | ~ m1_pre_topc(X0_58,X2_58)
    | ~ m1_pre_topc(X1_58,X2_58)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58))))
    | v2_struct_0(X2_58)
    | v2_struct_0(X3_58)
    | ~ v2_pre_topc(X2_58)
    | ~ v2_pre_topc(X3_58)
    | ~ l1_pre_topc(X2_58)
    | ~ l1_pre_topc(X3_58)
    | u1_struct_0(X3_58) != u1_struct_0(sK1)
    | u1_struct_0(X1_58) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X1_58),u1_struct_0(X3_58),sK4,u1_struct_0(X0_58)) = k3_tmap_1(X2_58,X3_58,X1_58,X0_58,sK4) ),
    inference(subtyping,[status(esa)],[c_336])).

cnf(c_1769,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK1)
    | u1_struct_0(X1_58) != u1_struct_0(sK3)
    | k2_partfun1(u1_struct_0(X1_58),u1_struct_0(X0_58),sK4,u1_struct_0(X2_58)) = k3_tmap_1(X3_58,X0_58,X1_58,X2_58,sK4)
    | m1_pre_topc(X2_58,X1_58) != iProver_top
    | m1_pre_topc(X2_58,X3_58) != iProver_top
    | m1_pre_topc(X1_58,X3_58) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X3_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X3_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X3_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1189])).

cnf(c_2332,plain,
    ( u1_struct_0(X0_58) != u1_struct_0(sK1)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_58),sK4,u1_struct_0(X1_58)) = k3_tmap_1(X2_58,X0_58,sK3,X1_58,sK4)
    | m1_pre_topc(X1_58,X2_58) != iProver_top
    | m1_pre_topc(X1_58,sK3) != iProver_top
    | m1_pre_topc(sK3,X2_58) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_58)))) != iProver_top
    | v2_struct_0(X2_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X2_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X2_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1769])).

cnf(c_2602,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_58)) = k3_tmap_1(X1_58,sK1,sK3,X0_58,sK4)
    | m1_pre_topc(X0_58,X1_58) != iProver_top
    | m1_pre_topc(X0_58,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_58) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2332])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_1188,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
    inference(subtyping,[status(esa)],[c_383])).

cnf(c_1770,plain,
    ( k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1188])).

cnf(c_2272,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(superposition,[status(thm)],[c_1758,c_1770])).

cnf(c_2603,plain,
    ( k3_tmap_1(X0_58,sK1,sK3,X1_58,sK4) = k7_relat_1(sK4,u1_struct_0(X1_58))
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_58) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2602,c_2272])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2681,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k3_tmap_1(X0_58,sK1,sK3,X1_58,sK4) = k7_relat_1(sK4,u1_struct_0(X1_58))
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2603,c_35,c_36,c_37,c_44])).

cnf(c_2682,plain,
    ( k3_tmap_1(X0_58,sK1,sK3,X1_58,sK4) = k7_relat_1(sK4,u1_struct_0(X1_58))
    | m1_pre_topc(X1_58,X0_58) != iProver_top
    | m1_pre_topc(X1_58,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_2681])).

cnf(c_2696,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1761,c_2682])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_45,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2812,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2696,c_32,c_33,c_34,c_41,c_45])).

cnf(c_15,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1204,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2815,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_2812,c_1204])).

cnf(c_3064,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k10_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_2956,c_2815])).

cnf(c_5240,plain,
    ( k3_xboole_0(u1_struct_0(sK2),k10_relat_1(sK4,sK5)) != k10_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_5236,c_3064])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1217,plain,
    ( k3_xboole_0(X0_57,X1_57) = k3_xboole_0(X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1203,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1755,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1203])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1216,plain,
    ( ~ r1_tarski(X0_57,X1_57)
    | k3_xboole_0(X0_57,X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1743,plain,
    ( k3_xboole_0(X0_57,X1_57) = X0_57
    | r1_tarski(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_2209,plain,
    ( k3_xboole_0(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1755,c_1743])).

cnf(c_2211,plain,
    ( k3_xboole_0(u1_struct_0(sK2),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1217,c_2209])).

cnf(c_3065,plain,
    ( k3_xboole_0(u1_struct_0(sK2),k10_relat_1(sK4,sK5)) = k10_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_2956,c_2211])).

cnf(c_5241,plain,
    ( k10_relat_1(sK4,sK5) != k10_relat_1(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_5240,c_3065])).

cnf(c_5242,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5241])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.81/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.81/1.00  
% 2.81/1.00  ------  iProver source info
% 2.81/1.00  
% 2.81/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.81/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.81/1.00  git: non_committed_changes: false
% 2.81/1.00  git: last_make_outside_of_git: false
% 2.81/1.00  
% 2.81/1.00  ------ 
% 2.81/1.00  
% 2.81/1.00  ------ Input Options
% 2.81/1.00  
% 2.81/1.00  --out_options                           all
% 2.81/1.00  --tptp_safe_out                         true
% 2.81/1.00  --problem_path                          ""
% 2.81/1.00  --include_path                          ""
% 2.81/1.00  --clausifier                            res/vclausify_rel
% 2.81/1.00  --clausifier_options                    --mode clausify
% 2.81/1.00  --stdin                                 false
% 2.81/1.00  --stats_out                             all
% 2.81/1.00  
% 2.81/1.00  ------ General Options
% 2.81/1.00  
% 2.81/1.00  --fof                                   false
% 2.81/1.00  --time_out_real                         305.
% 2.81/1.00  --time_out_virtual                      -1.
% 2.81/1.00  --symbol_type_check                     false
% 2.81/1.00  --clausify_out                          false
% 2.81/1.00  --sig_cnt_out                           false
% 2.81/1.00  --trig_cnt_out                          false
% 2.81/1.00  --trig_cnt_out_tolerance                1.
% 2.81/1.00  --trig_cnt_out_sk_spl                   false
% 2.81/1.00  --abstr_cl_out                          false
% 2.81/1.00  
% 2.81/1.00  ------ Global Options
% 2.81/1.00  
% 2.81/1.00  --schedule                              default
% 2.81/1.00  --add_important_lit                     false
% 2.81/1.00  --prop_solver_per_cl                    1000
% 2.81/1.00  --min_unsat_core                        false
% 2.81/1.00  --soft_assumptions                      false
% 2.81/1.00  --soft_lemma_size                       3
% 2.81/1.00  --prop_impl_unit_size                   0
% 2.81/1.00  --prop_impl_unit                        []
% 2.81/1.00  --share_sel_clauses                     true
% 2.81/1.00  --reset_solvers                         false
% 2.81/1.00  --bc_imp_inh                            [conj_cone]
% 2.81/1.00  --conj_cone_tolerance                   3.
% 2.81/1.00  --extra_neg_conj                        none
% 2.81/1.00  --large_theory_mode                     true
% 2.81/1.00  --prolific_symb_bound                   200
% 2.81/1.00  --lt_threshold                          2000
% 2.81/1.00  --clause_weak_htbl                      true
% 2.81/1.00  --gc_record_bc_elim                     false
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing Options
% 2.81/1.00  
% 2.81/1.00  --preprocessing_flag                    true
% 2.81/1.00  --time_out_prep_mult                    0.1
% 2.81/1.00  --splitting_mode                        input
% 2.81/1.00  --splitting_grd                         true
% 2.81/1.00  --splitting_cvd                         false
% 2.81/1.00  --splitting_cvd_svl                     false
% 2.81/1.00  --splitting_nvd                         32
% 2.81/1.00  --sub_typing                            true
% 2.81/1.00  --prep_gs_sim                           true
% 2.81/1.00  --prep_unflatten                        true
% 2.81/1.00  --prep_res_sim                          true
% 2.81/1.00  --prep_upred                            true
% 2.81/1.00  --prep_sem_filter                       exhaustive
% 2.81/1.00  --prep_sem_filter_out                   false
% 2.81/1.00  --pred_elim                             true
% 2.81/1.00  --res_sim_input                         true
% 2.81/1.00  --eq_ax_congr_red                       true
% 2.81/1.00  --pure_diseq_elim                       true
% 2.81/1.00  --brand_transform                       false
% 2.81/1.00  --non_eq_to_eq                          false
% 2.81/1.00  --prep_def_merge                        true
% 2.81/1.00  --prep_def_merge_prop_impl              false
% 2.81/1.00  --prep_def_merge_mbd                    true
% 2.81/1.00  --prep_def_merge_tr_red                 false
% 2.81/1.00  --prep_def_merge_tr_cl                  false
% 2.81/1.00  --smt_preprocessing                     true
% 2.81/1.00  --smt_ac_axioms                         fast
% 2.81/1.00  --preprocessed_out                      false
% 2.81/1.00  --preprocessed_stats                    false
% 2.81/1.00  
% 2.81/1.00  ------ Abstraction refinement Options
% 2.81/1.00  
% 2.81/1.00  --abstr_ref                             []
% 2.81/1.00  --abstr_ref_prep                        false
% 2.81/1.00  --abstr_ref_until_sat                   false
% 2.81/1.00  --abstr_ref_sig_restrict                funpre
% 2.81/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/1.00  --abstr_ref_under                       []
% 2.81/1.00  
% 2.81/1.00  ------ SAT Options
% 2.81/1.00  
% 2.81/1.00  --sat_mode                              false
% 2.81/1.00  --sat_fm_restart_options                ""
% 2.81/1.00  --sat_gr_def                            false
% 2.81/1.00  --sat_epr_types                         true
% 2.81/1.00  --sat_non_cyclic_types                  false
% 2.81/1.00  --sat_finite_models                     false
% 2.81/1.00  --sat_fm_lemmas                         false
% 2.81/1.00  --sat_fm_prep                           false
% 2.81/1.00  --sat_fm_uc_incr                        true
% 2.81/1.00  --sat_out_model                         small
% 2.81/1.00  --sat_out_clauses                       false
% 2.81/1.00  
% 2.81/1.00  ------ QBF Options
% 2.81/1.00  
% 2.81/1.00  --qbf_mode                              false
% 2.81/1.00  --qbf_elim_univ                         false
% 2.81/1.00  --qbf_dom_inst                          none
% 2.81/1.00  --qbf_dom_pre_inst                      false
% 2.81/1.00  --qbf_sk_in                             false
% 2.81/1.00  --qbf_pred_elim                         true
% 2.81/1.00  --qbf_split                             512
% 2.81/1.00  
% 2.81/1.00  ------ BMC1 Options
% 2.81/1.00  
% 2.81/1.00  --bmc1_incremental                      false
% 2.81/1.00  --bmc1_axioms                           reachable_all
% 2.81/1.00  --bmc1_min_bound                        0
% 2.81/1.00  --bmc1_max_bound                        -1
% 2.81/1.00  --bmc1_max_bound_default                -1
% 2.81/1.00  --bmc1_symbol_reachability              true
% 2.81/1.00  --bmc1_property_lemmas                  false
% 2.81/1.00  --bmc1_k_induction                      false
% 2.81/1.00  --bmc1_non_equiv_states                 false
% 2.81/1.00  --bmc1_deadlock                         false
% 2.81/1.00  --bmc1_ucm                              false
% 2.81/1.00  --bmc1_add_unsat_core                   none
% 2.81/1.00  --bmc1_unsat_core_children              false
% 2.81/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/1.00  --bmc1_out_stat                         full
% 2.81/1.00  --bmc1_ground_init                      false
% 2.81/1.00  --bmc1_pre_inst_next_state              false
% 2.81/1.00  --bmc1_pre_inst_state                   false
% 2.81/1.00  --bmc1_pre_inst_reach_state             false
% 2.81/1.00  --bmc1_out_unsat_core                   false
% 2.81/1.00  --bmc1_aig_witness_out                  false
% 2.81/1.00  --bmc1_verbose                          false
% 2.81/1.00  --bmc1_dump_clauses_tptp                false
% 2.81/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.81/1.00  --bmc1_dump_file                        -
% 2.81/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.81/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.81/1.00  --bmc1_ucm_extend_mode                  1
% 2.81/1.00  --bmc1_ucm_init_mode                    2
% 2.81/1.00  --bmc1_ucm_cone_mode                    none
% 2.81/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.81/1.00  --bmc1_ucm_relax_model                  4
% 2.81/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.81/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/1.00  --bmc1_ucm_layered_model                none
% 2.81/1.00  --bmc1_ucm_max_lemma_size               10
% 2.81/1.00  
% 2.81/1.00  ------ AIG Options
% 2.81/1.00  
% 2.81/1.00  --aig_mode                              false
% 2.81/1.00  
% 2.81/1.00  ------ Instantiation Options
% 2.81/1.00  
% 2.81/1.00  --instantiation_flag                    true
% 2.81/1.00  --inst_sos_flag                         false
% 2.81/1.00  --inst_sos_phase                        true
% 2.81/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/1.00  --inst_lit_sel_side                     num_symb
% 2.81/1.00  --inst_solver_per_active                1400
% 2.81/1.00  --inst_solver_calls_frac                1.
% 2.81/1.00  --inst_passive_queue_type               priority_queues
% 2.81/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/1.00  --inst_passive_queues_freq              [25;2]
% 2.81/1.00  --inst_dismatching                      true
% 2.81/1.00  --inst_eager_unprocessed_to_passive     true
% 2.81/1.00  --inst_prop_sim_given                   true
% 2.81/1.00  --inst_prop_sim_new                     false
% 2.81/1.00  --inst_subs_new                         false
% 2.81/1.00  --inst_eq_res_simp                      false
% 2.81/1.00  --inst_subs_given                       false
% 2.81/1.00  --inst_orphan_elimination               true
% 2.81/1.00  --inst_learning_loop_flag               true
% 2.81/1.00  --inst_learning_start                   3000
% 2.81/1.00  --inst_learning_factor                  2
% 2.81/1.00  --inst_start_prop_sim_after_learn       3
% 2.81/1.00  --inst_sel_renew                        solver
% 2.81/1.00  --inst_lit_activity_flag                true
% 2.81/1.00  --inst_restr_to_given                   false
% 2.81/1.00  --inst_activity_threshold               500
% 2.81/1.00  --inst_out_proof                        true
% 2.81/1.00  
% 2.81/1.00  ------ Resolution Options
% 2.81/1.00  
% 2.81/1.00  --resolution_flag                       true
% 2.81/1.00  --res_lit_sel                           adaptive
% 2.81/1.00  --res_lit_sel_side                      none
% 2.81/1.00  --res_ordering                          kbo
% 2.81/1.00  --res_to_prop_solver                    active
% 2.81/1.00  --res_prop_simpl_new                    false
% 2.81/1.00  --res_prop_simpl_given                  true
% 2.81/1.00  --res_passive_queue_type                priority_queues
% 2.81/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/1.00  --res_passive_queues_freq               [15;5]
% 2.81/1.00  --res_forward_subs                      full
% 2.81/1.00  --res_backward_subs                     full
% 2.81/1.00  --res_forward_subs_resolution           true
% 2.81/1.00  --res_backward_subs_resolution          true
% 2.81/1.00  --res_orphan_elimination                true
% 2.81/1.00  --res_time_limit                        2.
% 2.81/1.00  --res_out_proof                         true
% 2.81/1.00  
% 2.81/1.00  ------ Superposition Options
% 2.81/1.00  
% 2.81/1.00  --superposition_flag                    true
% 2.81/1.00  --sup_passive_queue_type                priority_queues
% 2.81/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.81/1.00  --demod_completeness_check              fast
% 2.81/1.00  --demod_use_ground                      true
% 2.81/1.00  --sup_to_prop_solver                    passive
% 2.81/1.00  --sup_prop_simpl_new                    true
% 2.81/1.00  --sup_prop_simpl_given                  true
% 2.81/1.00  --sup_fun_splitting                     false
% 2.81/1.00  --sup_smt_interval                      50000
% 2.81/1.00  
% 2.81/1.00  ------ Superposition Simplification Setup
% 2.81/1.00  
% 2.81/1.00  --sup_indices_passive                   []
% 2.81/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_full_bw                           [BwDemod]
% 2.81/1.00  --sup_immed_triv                        [TrivRules]
% 2.81/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_immed_bw_main                     []
% 2.81/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.00  
% 2.81/1.00  ------ Combination Options
% 2.81/1.00  
% 2.81/1.00  --comb_res_mult                         3
% 2.81/1.00  --comb_sup_mult                         2
% 2.81/1.00  --comb_inst_mult                        10
% 2.81/1.00  
% 2.81/1.00  ------ Debug Options
% 2.81/1.00  
% 2.81/1.00  --dbg_backtrace                         false
% 2.81/1.00  --dbg_dump_prop_clauses                 false
% 2.81/1.00  --dbg_dump_prop_clauses_file            -
% 2.81/1.00  --dbg_out_stat                          false
% 2.81/1.00  ------ Parsing...
% 2.81/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.81/1.00  ------ Proving...
% 2.81/1.00  ------ Problem Properties 
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  clauses                                 30
% 2.81/1.00  conjectures                             15
% 2.81/1.00  EPR                                     11
% 2.81/1.00  Horn                                    29
% 2.81/1.00  unary                                   16
% 2.81/1.00  binary                                  8
% 2.81/1.00  lits                                    61
% 2.81/1.00  lits eq                                 9
% 2.81/1.00  fd_pure                                 0
% 2.81/1.00  fd_pseudo                               0
% 2.81/1.00  fd_cond                                 0
% 2.81/1.00  fd_pseudo_cond                          0
% 2.81/1.00  AC symbols                              0
% 2.81/1.00  
% 2.81/1.00  ------ Schedule dynamic 5 is on 
% 2.81/1.00  
% 2.81/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  ------ 
% 2.81/1.00  Current options:
% 2.81/1.00  ------ 
% 2.81/1.00  
% 2.81/1.00  ------ Input Options
% 2.81/1.00  
% 2.81/1.00  --out_options                           all
% 2.81/1.00  --tptp_safe_out                         true
% 2.81/1.00  --problem_path                          ""
% 2.81/1.00  --include_path                          ""
% 2.81/1.00  --clausifier                            res/vclausify_rel
% 2.81/1.00  --clausifier_options                    --mode clausify
% 2.81/1.00  --stdin                                 false
% 2.81/1.00  --stats_out                             all
% 2.81/1.00  
% 2.81/1.00  ------ General Options
% 2.81/1.00  
% 2.81/1.00  --fof                                   false
% 2.81/1.00  --time_out_real                         305.
% 2.81/1.00  --time_out_virtual                      -1.
% 2.81/1.00  --symbol_type_check                     false
% 2.81/1.00  --clausify_out                          false
% 2.81/1.00  --sig_cnt_out                           false
% 2.81/1.00  --trig_cnt_out                          false
% 2.81/1.00  --trig_cnt_out_tolerance                1.
% 2.81/1.00  --trig_cnt_out_sk_spl                   false
% 2.81/1.00  --abstr_cl_out                          false
% 2.81/1.00  
% 2.81/1.00  ------ Global Options
% 2.81/1.00  
% 2.81/1.00  --schedule                              default
% 2.81/1.00  --add_important_lit                     false
% 2.81/1.00  --prop_solver_per_cl                    1000
% 2.81/1.00  --min_unsat_core                        false
% 2.81/1.00  --soft_assumptions                      false
% 2.81/1.00  --soft_lemma_size                       3
% 2.81/1.00  --prop_impl_unit_size                   0
% 2.81/1.00  --prop_impl_unit                        []
% 2.81/1.00  --share_sel_clauses                     true
% 2.81/1.00  --reset_solvers                         false
% 2.81/1.00  --bc_imp_inh                            [conj_cone]
% 2.81/1.00  --conj_cone_tolerance                   3.
% 2.81/1.00  --extra_neg_conj                        none
% 2.81/1.00  --large_theory_mode                     true
% 2.81/1.00  --prolific_symb_bound                   200
% 2.81/1.00  --lt_threshold                          2000
% 2.81/1.00  --clause_weak_htbl                      true
% 2.81/1.00  --gc_record_bc_elim                     false
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing Options
% 2.81/1.00  
% 2.81/1.00  --preprocessing_flag                    true
% 2.81/1.00  --time_out_prep_mult                    0.1
% 2.81/1.00  --splitting_mode                        input
% 2.81/1.00  --splitting_grd                         true
% 2.81/1.00  --splitting_cvd                         false
% 2.81/1.00  --splitting_cvd_svl                     false
% 2.81/1.00  --splitting_nvd                         32
% 2.81/1.00  --sub_typing                            true
% 2.81/1.00  --prep_gs_sim                           true
% 2.81/1.00  --prep_unflatten                        true
% 2.81/1.00  --prep_res_sim                          true
% 2.81/1.00  --prep_upred                            true
% 2.81/1.00  --prep_sem_filter                       exhaustive
% 2.81/1.00  --prep_sem_filter_out                   false
% 2.81/1.00  --pred_elim                             true
% 2.81/1.00  --res_sim_input                         true
% 2.81/1.00  --eq_ax_congr_red                       true
% 2.81/1.00  --pure_diseq_elim                       true
% 2.81/1.00  --brand_transform                       false
% 2.81/1.00  --non_eq_to_eq                          false
% 2.81/1.00  --prep_def_merge                        true
% 2.81/1.00  --prep_def_merge_prop_impl              false
% 2.81/1.00  --prep_def_merge_mbd                    true
% 2.81/1.00  --prep_def_merge_tr_red                 false
% 2.81/1.00  --prep_def_merge_tr_cl                  false
% 2.81/1.00  --smt_preprocessing                     true
% 2.81/1.00  --smt_ac_axioms                         fast
% 2.81/1.00  --preprocessed_out                      false
% 2.81/1.00  --preprocessed_stats                    false
% 2.81/1.00  
% 2.81/1.00  ------ Abstraction refinement Options
% 2.81/1.00  
% 2.81/1.00  --abstr_ref                             []
% 2.81/1.00  --abstr_ref_prep                        false
% 2.81/1.00  --abstr_ref_until_sat                   false
% 2.81/1.00  --abstr_ref_sig_restrict                funpre
% 2.81/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/1.00  --abstr_ref_under                       []
% 2.81/1.00  
% 2.81/1.00  ------ SAT Options
% 2.81/1.00  
% 2.81/1.00  --sat_mode                              false
% 2.81/1.00  --sat_fm_restart_options                ""
% 2.81/1.00  --sat_gr_def                            false
% 2.81/1.00  --sat_epr_types                         true
% 2.81/1.00  --sat_non_cyclic_types                  false
% 2.81/1.00  --sat_finite_models                     false
% 2.81/1.00  --sat_fm_lemmas                         false
% 2.81/1.00  --sat_fm_prep                           false
% 2.81/1.00  --sat_fm_uc_incr                        true
% 2.81/1.00  --sat_out_model                         small
% 2.81/1.00  --sat_out_clauses                       false
% 2.81/1.00  
% 2.81/1.00  ------ QBF Options
% 2.81/1.00  
% 2.81/1.00  --qbf_mode                              false
% 2.81/1.00  --qbf_elim_univ                         false
% 2.81/1.00  --qbf_dom_inst                          none
% 2.81/1.00  --qbf_dom_pre_inst                      false
% 2.81/1.00  --qbf_sk_in                             false
% 2.81/1.00  --qbf_pred_elim                         true
% 2.81/1.00  --qbf_split                             512
% 2.81/1.00  
% 2.81/1.00  ------ BMC1 Options
% 2.81/1.00  
% 2.81/1.00  --bmc1_incremental                      false
% 2.81/1.00  --bmc1_axioms                           reachable_all
% 2.81/1.00  --bmc1_min_bound                        0
% 2.81/1.00  --bmc1_max_bound                        -1
% 2.81/1.00  --bmc1_max_bound_default                -1
% 2.81/1.00  --bmc1_symbol_reachability              true
% 2.81/1.00  --bmc1_property_lemmas                  false
% 2.81/1.00  --bmc1_k_induction                      false
% 2.81/1.00  --bmc1_non_equiv_states                 false
% 2.81/1.00  --bmc1_deadlock                         false
% 2.81/1.00  --bmc1_ucm                              false
% 2.81/1.00  --bmc1_add_unsat_core                   none
% 2.81/1.00  --bmc1_unsat_core_children              false
% 2.81/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/1.00  --bmc1_out_stat                         full
% 2.81/1.00  --bmc1_ground_init                      false
% 2.81/1.00  --bmc1_pre_inst_next_state              false
% 2.81/1.00  --bmc1_pre_inst_state                   false
% 2.81/1.00  --bmc1_pre_inst_reach_state             false
% 2.81/1.00  --bmc1_out_unsat_core                   false
% 2.81/1.00  --bmc1_aig_witness_out                  false
% 2.81/1.00  --bmc1_verbose                          false
% 2.81/1.00  --bmc1_dump_clauses_tptp                false
% 2.81/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.81/1.00  --bmc1_dump_file                        -
% 2.81/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.81/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.81/1.00  --bmc1_ucm_extend_mode                  1
% 2.81/1.00  --bmc1_ucm_init_mode                    2
% 2.81/1.00  --bmc1_ucm_cone_mode                    none
% 2.81/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.81/1.00  --bmc1_ucm_relax_model                  4
% 2.81/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.81/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/1.00  --bmc1_ucm_layered_model                none
% 2.81/1.00  --bmc1_ucm_max_lemma_size               10
% 2.81/1.00  
% 2.81/1.00  ------ AIG Options
% 2.81/1.00  
% 2.81/1.00  --aig_mode                              false
% 2.81/1.00  
% 2.81/1.00  ------ Instantiation Options
% 2.81/1.00  
% 2.81/1.00  --instantiation_flag                    true
% 2.81/1.00  --inst_sos_flag                         false
% 2.81/1.00  --inst_sos_phase                        true
% 2.81/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/1.00  --inst_lit_sel_side                     none
% 2.81/1.00  --inst_solver_per_active                1400
% 2.81/1.00  --inst_solver_calls_frac                1.
% 2.81/1.00  --inst_passive_queue_type               priority_queues
% 2.81/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/1.00  --inst_passive_queues_freq              [25;2]
% 2.81/1.00  --inst_dismatching                      true
% 2.81/1.00  --inst_eager_unprocessed_to_passive     true
% 2.81/1.00  --inst_prop_sim_given                   true
% 2.81/1.00  --inst_prop_sim_new                     false
% 2.81/1.00  --inst_subs_new                         false
% 2.81/1.00  --inst_eq_res_simp                      false
% 2.81/1.00  --inst_subs_given                       false
% 2.81/1.00  --inst_orphan_elimination               true
% 2.81/1.00  --inst_learning_loop_flag               true
% 2.81/1.00  --inst_learning_start                   3000
% 2.81/1.00  --inst_learning_factor                  2
% 2.81/1.00  --inst_start_prop_sim_after_learn       3
% 2.81/1.00  --inst_sel_renew                        solver
% 2.81/1.00  --inst_lit_activity_flag                true
% 2.81/1.00  --inst_restr_to_given                   false
% 2.81/1.00  --inst_activity_threshold               500
% 2.81/1.00  --inst_out_proof                        true
% 2.81/1.00  
% 2.81/1.00  ------ Resolution Options
% 2.81/1.00  
% 2.81/1.00  --resolution_flag                       false
% 2.81/1.00  --res_lit_sel                           adaptive
% 2.81/1.00  --res_lit_sel_side                      none
% 2.81/1.00  --res_ordering                          kbo
% 2.81/1.00  --res_to_prop_solver                    active
% 2.81/1.00  --res_prop_simpl_new                    false
% 2.81/1.00  --res_prop_simpl_given                  true
% 2.81/1.00  --res_passive_queue_type                priority_queues
% 2.81/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/1.00  --res_passive_queues_freq               [15;5]
% 2.81/1.00  --res_forward_subs                      full
% 2.81/1.00  --res_backward_subs                     full
% 2.81/1.00  --res_forward_subs_resolution           true
% 2.81/1.00  --res_backward_subs_resolution          true
% 2.81/1.00  --res_orphan_elimination                true
% 2.81/1.00  --res_time_limit                        2.
% 2.81/1.00  --res_out_proof                         true
% 2.81/1.00  
% 2.81/1.00  ------ Superposition Options
% 2.81/1.00  
% 2.81/1.00  --superposition_flag                    true
% 2.81/1.00  --sup_passive_queue_type                priority_queues
% 2.81/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.81/1.00  --demod_completeness_check              fast
% 2.81/1.00  --demod_use_ground                      true
% 2.81/1.00  --sup_to_prop_solver                    passive
% 2.81/1.00  --sup_prop_simpl_new                    true
% 2.81/1.00  --sup_prop_simpl_given                  true
% 2.81/1.00  --sup_fun_splitting                     false
% 2.81/1.00  --sup_smt_interval                      50000
% 2.81/1.00  
% 2.81/1.00  ------ Superposition Simplification Setup
% 2.81/1.00  
% 2.81/1.00  --sup_indices_passive                   []
% 2.81/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_full_bw                           [BwDemod]
% 2.81/1.00  --sup_immed_triv                        [TrivRules]
% 2.81/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_immed_bw_main                     []
% 2.81/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.00  
% 2.81/1.00  ------ Combination Options
% 2.81/1.00  
% 2.81/1.00  --comb_res_mult                         3
% 2.81/1.00  --comb_sup_mult                         2
% 2.81/1.00  --comb_inst_mult                        10
% 2.81/1.00  
% 2.81/1.00  ------ Debug Options
% 2.81/1.00  
% 2.81/1.00  --dbg_backtrace                         false
% 2.81/1.00  --dbg_dump_prop_clauses                 false
% 2.81/1.00  --dbg_dump_prop_clauses_file            -
% 2.81/1.00  --dbg_out_stat                          false
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  ------ Proving...
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  % SZS status Theorem for theBenchmark.p
% 2.81/1.00  
% 2.81/1.00   Resolution empty clause
% 2.81/1.00  
% 2.81/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  fof(f14,conjecture,(
% 2.81/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f15,negated_conjecture,(
% 2.81/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.81/1.00    inference(negated_conjecture,[],[f14])).
% 2.81/1.00  
% 2.81/1.00  fof(f33,plain,(
% 2.81/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.81/1.00    inference(ennf_transformation,[],[f15])).
% 2.81/1.00  
% 2.81/1.00  fof(f34,plain,(
% 2.81/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.81/1.00    inference(flattening,[],[f33])).
% 2.81/1.00  
% 2.81/1.00  fof(f41,plain,(
% 2.81/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5),u1_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f40,plain,(
% 2.81/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f39,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f38,plain,(
% 2.81/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f37,plain,(
% 2.81/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f36,plain,(
% 2.81/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f42,plain,(
% 2.81/1.00    (((((k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.81/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f34,f41,f40,f39,f38,f37,f36])).
% 2.81/1.00  
% 2.81/1.00  fof(f70,plain,(
% 2.81/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f9,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f16,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.81/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.81/1.00  
% 2.81/1.00  fof(f25,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.81/1.00    inference(ennf_transformation,[],[f16])).
% 2.81/1.00  
% 2.81/1.00  fof(f53,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.81/1.00    inference(cnf_transformation,[],[f25])).
% 2.81/1.00  
% 2.81/1.00  fof(f7,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f22,plain,(
% 2.81/1.00    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 2.81/1.00    inference(ennf_transformation,[],[f7])).
% 2.81/1.00  
% 2.81/1.00  fof(f23,plain,(
% 2.81/1.00    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 2.81/1.00    inference(flattening,[],[f22])).
% 2.81/1.00  
% 2.81/1.00  fof(f51,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (v5_relat_1(k7_relat_1(X2,X0),X1) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f23])).
% 2.81/1.00  
% 2.81/1.00  fof(f5,axiom,(
% 2.81/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f20,plain,(
% 2.81/1.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.81/1.00    inference(ennf_transformation,[],[f5])).
% 2.81/1.00  
% 2.81/1.00  fof(f48,plain,(
% 2.81/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f20])).
% 2.81/1.00  
% 2.81/1.00  fof(f3,axiom,(
% 2.81/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f18,plain,(
% 2.81/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.81/1.00    inference(ennf_transformation,[],[f3])).
% 2.81/1.00  
% 2.81/1.00  fof(f35,plain,(
% 2.81/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.81/1.00    inference(nnf_transformation,[],[f18])).
% 2.81/1.00  
% 2.81/1.00  fof(f45,plain,(
% 2.81/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f35])).
% 2.81/1.00  
% 2.81/1.00  fof(f11,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f27,plain,(
% 2.81/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.81/1.00    inference(ennf_transformation,[],[f11])).
% 2.81/1.00  
% 2.81/1.00  fof(f28,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.81/1.00    inference(flattening,[],[f27])).
% 2.81/1.00  
% 2.81/1.00  fof(f55,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f28])).
% 2.81/1.00  
% 2.81/1.00  fof(f10,axiom,(
% 2.81/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f26,plain,(
% 2.81/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.81/1.00    inference(ennf_transformation,[],[f10])).
% 2.81/1.00  
% 2.81/1.00  fof(f54,plain,(
% 2.81/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.81/1.00    inference(cnf_transformation,[],[f26])).
% 2.81/1.00  
% 2.81/1.00  fof(f4,axiom,(
% 2.81/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f19,plain,(
% 2.81/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.81/1.00    inference(ennf_transformation,[],[f4])).
% 2.81/1.00  
% 2.81/1.00  fof(f47,plain,(
% 2.81/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f19])).
% 2.81/1.00  
% 2.81/1.00  fof(f8,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f24,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.81/1.00    inference(ennf_transformation,[],[f8])).
% 2.81/1.00  
% 2.81/1.00  fof(f52,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.81/1.00    inference(cnf_transformation,[],[f24])).
% 2.81/1.00  
% 2.81/1.00  fof(f6,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f21,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 2.81/1.00    inference(ennf_transformation,[],[f6])).
% 2.81/1.00  
% 2.81/1.00  fof(f49,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f21])).
% 2.81/1.00  
% 2.81/1.00  fof(f65,plain,(
% 2.81/1.00    m1_pre_topc(sK2,sK0)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f13,axiom,(
% 2.81/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f31,plain,(
% 2.81/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.81/1.00    inference(ennf_transformation,[],[f13])).
% 2.81/1.00  
% 2.81/1.00  fof(f32,plain,(
% 2.81/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.81/1.00    inference(flattening,[],[f31])).
% 2.81/1.00  
% 2.81/1.00  fof(f57,plain,(
% 2.81/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f32])).
% 2.81/1.00  
% 2.81/1.00  fof(f69,plain,(
% 2.81/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f68,plain,(
% 2.81/1.00    v1_funct_1(sK4)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f12,axiom,(
% 2.81/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f29,plain,(
% 2.81/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.81/1.00    inference(ennf_transformation,[],[f12])).
% 2.81/1.00  
% 2.81/1.00  fof(f30,plain,(
% 2.81/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.81/1.00    inference(flattening,[],[f29])).
% 2.81/1.00  
% 2.81/1.00  fof(f56,plain,(
% 2.81/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f30])).
% 2.81/1.00  
% 2.81/1.00  fof(f61,plain,(
% 2.81/1.00    ~v2_struct_0(sK1)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f62,plain,(
% 2.81/1.00    v2_pre_topc(sK1)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f63,plain,(
% 2.81/1.00    l1_pre_topc(sK1)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f58,plain,(
% 2.81/1.00    ~v2_struct_0(sK0)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f59,plain,(
% 2.81/1.00    v2_pre_topc(sK0)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f60,plain,(
% 2.81/1.00    l1_pre_topc(sK0)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f67,plain,(
% 2.81/1.00    m1_pre_topc(sK3,sK0)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f71,plain,(
% 2.81/1.00    m1_pre_topc(sK2,sK3)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f74,plain,(
% 2.81/1.00    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f1,axiom,(
% 2.81/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f43,plain,(
% 2.81/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f1])).
% 2.81/1.00  
% 2.81/1.00  fof(f73,plain,(
% 2.81/1.00    r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2))),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f2,axiom,(
% 2.81/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f17,plain,(
% 2.81/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.81/1.00    inference(ennf_transformation,[],[f2])).
% 2.81/1.00  
% 2.81/1.00  fof(f44,plain,(
% 2.81/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f17])).
% 2.81/1.00  
% 2.81/1.00  cnf(c_19,negated_conjecture,
% 2.81/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.81/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1200,negated_conjecture,
% 2.81/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1758,plain,
% 2.81/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_10,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 2.81/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1207,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.81/1.00      | v5_relat_1(X0_55,X1_57) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1752,plain,
% 2.81/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.81/1.00      | v5_relat_1(X0_55,X1_57) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2471,plain,
% 2.81/1.00      ( v5_relat_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1758,c_1752]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_7,plain,
% 2.81/1.00      ( ~ v5_relat_1(X0,X1)
% 2.81/1.00      | v5_relat_1(k7_relat_1(X0,X2),X1)
% 2.81/1.00      | ~ v1_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1210,plain,
% 2.81/1.00      ( ~ v5_relat_1(X0_55,X0_57)
% 2.81/1.00      | v5_relat_1(k7_relat_1(X0_55,X1_57),X0_57)
% 2.81/1.00      | ~ v1_relat_1(X0_55) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1749,plain,
% 2.81/1.00      ( v5_relat_1(X0_55,X0_57) != iProver_top
% 2.81/1.00      | v5_relat_1(k7_relat_1(X0_55,X1_57),X0_57) = iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1210]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5,plain,
% 2.81/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1212,plain,
% 2.81/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0_55,X0_57)),X0_57)
% 2.81/1.00      | ~ v1_relat_1(X0_55) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1747,plain,
% 2.81/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0_55,X0_57)),X0_57) = iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1212]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3,plain,
% 2.81/1.00      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1214,plain,
% 2.81/1.00      ( ~ v5_relat_1(X0_55,X0_57)
% 2.81/1.00      | r1_tarski(k2_relat_1(X0_55),X0_57)
% 2.81/1.00      | ~ v1_relat_1(X0_55) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1745,plain,
% 2.81/1.00      ( v5_relat_1(X0_55,X0_57) != iProver_top
% 2.81/1.00      | r1_tarski(k2_relat_1(X0_55),X0_57) = iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1214]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_12,plain,
% 2.81/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.81/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.81/1.00      | ~ v1_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1205,plain,
% 2.81/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.81/1.00      | ~ r1_tarski(k1_relat_1(X0_55),X0_57)
% 2.81/1.00      | ~ r1_tarski(k2_relat_1(X0_55),X1_57)
% 2.81/1.00      | ~ v1_relat_1(X0_55) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1754,plain,
% 2.81/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) = iProver_top
% 2.81/1.00      | r1_tarski(k1_relat_1(X0_55),X0_57) != iProver_top
% 2.81/1.00      | r1_tarski(k2_relat_1(X0_55),X1_57) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1205]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_11,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.81/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1206,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.81/1.00      | k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1753,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55)
% 2.81/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1206]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3373,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55)
% 2.81/1.00      | r1_tarski(k1_relat_1(X0_55),X0_57) != iProver_top
% 2.81/1.00      | r1_tarski(k2_relat_1(X0_55),X1_57) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1754,c_1753]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4047,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,X1_57,X0_55,X1_55) = k10_relat_1(X0_55,X1_55)
% 2.81/1.00      | v5_relat_1(X0_55,X1_57) != iProver_top
% 2.81/1.00      | r1_tarski(k1_relat_1(X0_55),X0_57) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1745,c_3373]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4176,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,X1_57,k7_relat_1(X0_55,X0_57),X1_55) = k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55)
% 2.81/1.00      | v5_relat_1(k7_relat_1(X0_55,X0_57),X1_57) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top
% 2.81/1.00      | v1_relat_1(k7_relat_1(X0_55,X0_57)) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1747,c_4047]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4,plain,
% 2.81/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1213,plain,
% 2.81/1.00      ( ~ v1_relat_1(X0_55) | v1_relat_1(k7_relat_1(X0_55,X0_57)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1264,plain,
% 2.81/1.00      ( v1_relat_1(X0_55) != iProver_top
% 2.81/1.00      | v1_relat_1(k7_relat_1(X0_55,X0_57)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1213]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4606,plain,
% 2.81/1.00      ( v1_relat_1(X0_55) != iProver_top
% 2.81/1.00      | v5_relat_1(k7_relat_1(X0_55,X0_57),X1_57) != iProver_top
% 2.81/1.00      | k8_relset_1(X0_57,X1_57,k7_relat_1(X0_55,X0_57),X1_55) = k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55) ),
% 2.81/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4176,c_1264]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4607,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,X1_57,k7_relat_1(X0_55,X0_57),X1_55) = k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55)
% 2.81/1.00      | v5_relat_1(k7_relat_1(X0_55,X0_57),X1_57) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(renaming,[status(thm)],[c_4606]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4615,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,X1_57,k7_relat_1(X0_55,X0_57),X1_55) = k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55)
% 2.81/1.00      | v5_relat_1(X0_55,X1_57) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1749,c_4607]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4731,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,u1_struct_0(sK1),k7_relat_1(sK4,X0_57),X0_55) = k10_relat_1(k7_relat_1(sK4,X0_57),X0_55)
% 2.81/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_2471,c_4615]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_9,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1208,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.81/1.00      | v1_relat_1(X0_55) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1751,plain,
% 2.81/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_55) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2466,plain,
% 2.81/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1758,c_1751]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_6,plain,
% 2.81/1.00      ( ~ v1_relat_1(X0)
% 2.81/1.00      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1211,plain,
% 2.81/1.00      ( ~ v1_relat_1(X0_55)
% 2.81/1.00      | k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55) = k3_xboole_0(X0_57,k10_relat_1(X0_55,X1_55)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1748,plain,
% 2.81/1.00      ( k10_relat_1(k7_relat_1(X0_55,X0_57),X1_55) = k3_xboole_0(X0_57,k10_relat_1(X0_55,X1_55))
% 2.81/1.00      | v1_relat_1(X0_55) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1211]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2896,plain,
% 2.81/1.00      ( k10_relat_1(k7_relat_1(sK4,X0_57),X0_55) = k3_xboole_0(X0_57,k10_relat_1(sK4,X0_55)) ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_2466,c_1748]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4734,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,u1_struct_0(sK1),k7_relat_1(sK4,X0_57),X0_55) = k3_xboole_0(X0_57,k10_relat_1(sK4,X0_55))
% 2.81/1.00      | v1_relat_1(sK4) != iProver_top ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_4731,c_2896]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_44,plain,
% 2.81/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1962,plain,
% 2.81/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.81/1.00      | v1_relat_1(sK4) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_1208]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1963,plain,
% 2.81/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1962]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5236,plain,
% 2.81/1.00      ( k8_relset_1(X0_57,u1_struct_0(sK1),k7_relat_1(sK4,X0_57),X0_55) = k3_xboole_0(X0_57,k10_relat_1(sK4,X0_55)) ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_4734,c_44,c_1963]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2956,plain,
% 2.81/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_55) = k10_relat_1(sK4,X0_55) ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1758,c_1753]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_24,negated_conjecture,
% 2.81/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1197,negated_conjecture,
% 2.81/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1761,plain,
% 2.81/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1197]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_14,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.81/1.00      | ~ m1_pre_topc(X3,X1)
% 2.81/1.00      | ~ m1_pre_topc(X3,X4)
% 2.81/1.00      | ~ m1_pre_topc(X1,X4)
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.81/1.00      | v2_struct_0(X4)
% 2.81/1.00      | v2_struct_0(X2)
% 2.81/1.00      | ~ v2_pre_topc(X2)
% 2.81/1.00      | ~ v2_pre_topc(X4)
% 2.81/1.00      | ~ l1_pre_topc(X2)
% 2.81/1.00      | ~ l1_pre_topc(X4)
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_20,negated_conjecture,
% 2.81/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_330,plain,
% 2.81/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.81/1.00      | ~ m1_pre_topc(X0,X2)
% 2.81/1.00      | ~ m1_pre_topc(X1,X2)
% 2.81/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 2.81/1.00      | v2_struct_0(X2)
% 2.81/1.00      | v2_struct_0(X4)
% 2.81/1.00      | ~ v2_pre_topc(X4)
% 2.81/1.00      | ~ v2_pre_topc(X2)
% 2.81/1.00      | ~ l1_pre_topc(X4)
% 2.81/1.00      | ~ l1_pre_topc(X2)
% 2.81/1.00      | ~ v1_funct_1(X3)
% 2.81/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 2.81/1.00      | u1_struct_0(X4) != u1_struct_0(sK1)
% 2.81/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 2.81/1.00      | sK4 != X3 ),
% 2.81/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_331,plain,
% 2.81/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.81/1.00      | ~ m1_pre_topc(X0,X2)
% 2.81/1.00      | ~ m1_pre_topc(X1,X2)
% 2.81/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.81/1.00      | v2_struct_0(X3)
% 2.81/1.00      | v2_struct_0(X2)
% 2.81/1.00      | ~ v2_pre_topc(X2)
% 2.81/1.00      | ~ v2_pre_topc(X3)
% 2.81/1.00      | ~ l1_pre_topc(X2)
% 2.81/1.00      | ~ l1_pre_topc(X3)
% 2.81/1.00      | ~ v1_funct_1(sK4)
% 2.81/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.81/1.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 2.81/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.81/1.00      inference(unflattening,[status(thm)],[c_330]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_21,negated_conjecture,
% 2.81/1.00      ( v1_funct_1(sK4) ),
% 2.81/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_335,plain,
% 2.81/1.00      ( ~ l1_pre_topc(X3)
% 2.81/1.00      | ~ l1_pre_topc(X2)
% 2.81/1.00      | ~ v2_pre_topc(X3)
% 2.81/1.00      | ~ v2_pre_topc(X2)
% 2.81/1.00      | v2_struct_0(X2)
% 2.81/1.00      | v2_struct_0(X3)
% 2.81/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.81/1.00      | ~ m1_pre_topc(X1,X2)
% 2.81/1.00      | ~ m1_pre_topc(X0,X2)
% 2.81/1.00      | ~ m1_pre_topc(X0,X1)
% 2.81/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.81/1.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 2.81/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.81/1.00      inference(global_propositional_subsumption,[status(thm)],[c_331,c_21]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_336,plain,
% 2.81/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.81/1.00      | ~ m1_pre_topc(X0,X2)
% 2.81/1.00      | ~ m1_pre_topc(X1,X2)
% 2.81/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 2.81/1.00      | v2_struct_0(X2)
% 2.81/1.00      | v2_struct_0(X3)
% 2.81/1.00      | ~ v2_pre_topc(X2)
% 2.81/1.00      | ~ v2_pre_topc(X3)
% 2.81/1.00      | ~ l1_pre_topc(X2)
% 2.81/1.00      | ~ l1_pre_topc(X3)
% 2.81/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK4,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK4)
% 2.81/1.00      | u1_struct_0(X3) != u1_struct_0(sK1)
% 2.81/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 2.81/1.00      inference(renaming,[status(thm)],[c_335]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1189,plain,
% 2.81/1.00      ( ~ m1_pre_topc(X0_58,X1_58)
% 2.81/1.00      | ~ m1_pre_topc(X0_58,X2_58)
% 2.81/1.00      | ~ m1_pre_topc(X1_58,X2_58)
% 2.81/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X3_58))))
% 2.81/1.00      | v2_struct_0(X2_58)
% 2.81/1.00      | v2_struct_0(X3_58)
% 2.81/1.00      | ~ v2_pre_topc(X2_58)
% 2.81/1.00      | ~ v2_pre_topc(X3_58)
% 2.81/1.00      | ~ l1_pre_topc(X2_58)
% 2.81/1.00      | ~ l1_pre_topc(X3_58)
% 2.81/1.00      | u1_struct_0(X3_58) != u1_struct_0(sK1)
% 2.81/1.00      | u1_struct_0(X1_58) != u1_struct_0(sK3)
% 2.81/1.00      | k2_partfun1(u1_struct_0(X1_58),u1_struct_0(X3_58),sK4,u1_struct_0(X0_58)) = k3_tmap_1(X2_58,X3_58,X1_58,X0_58,sK4) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_336]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1769,plain,
% 2.81/1.00      ( u1_struct_0(X0_58) != u1_struct_0(sK1)
% 2.81/1.00      | u1_struct_0(X1_58) != u1_struct_0(sK3)
% 2.81/1.00      | k2_partfun1(u1_struct_0(X1_58),u1_struct_0(X0_58),sK4,u1_struct_0(X2_58)) = k3_tmap_1(X3_58,X0_58,X1_58,X2_58,sK4)
% 2.81/1.00      | m1_pre_topc(X2_58,X1_58) != iProver_top
% 2.81/1.00      | m1_pre_topc(X2_58,X3_58) != iProver_top
% 2.81/1.00      | m1_pre_topc(X1_58,X3_58) != iProver_top
% 2.81/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_58),u1_struct_0(X0_58)))) != iProver_top
% 2.81/1.00      | v2_struct_0(X0_58) = iProver_top
% 2.81/1.00      | v2_struct_0(X3_58) = iProver_top
% 2.81/1.00      | v2_pre_topc(X0_58) != iProver_top
% 2.81/1.00      | v2_pre_topc(X3_58) != iProver_top
% 2.81/1.00      | l1_pre_topc(X0_58) != iProver_top
% 2.81/1.00      | l1_pre_topc(X3_58) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1189]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2332,plain,
% 2.81/1.00      ( u1_struct_0(X0_58) != u1_struct_0(sK1)
% 2.81/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X0_58),sK4,u1_struct_0(X1_58)) = k3_tmap_1(X2_58,X0_58,sK3,X1_58,sK4)
% 2.81/1.00      | m1_pre_topc(X1_58,X2_58) != iProver_top
% 2.81/1.00      | m1_pre_topc(X1_58,sK3) != iProver_top
% 2.81/1.00      | m1_pre_topc(sK3,X2_58) != iProver_top
% 2.81/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_58)))) != iProver_top
% 2.81/1.00      | v2_struct_0(X2_58) = iProver_top
% 2.81/1.00      | v2_struct_0(X0_58) = iProver_top
% 2.81/1.00      | v2_pre_topc(X2_58) != iProver_top
% 2.81/1.00      | v2_pre_topc(X0_58) != iProver_top
% 2.81/1.00      | l1_pre_topc(X2_58) != iProver_top
% 2.81/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 2.81/1.00      inference(equality_resolution,[status(thm)],[c_1769]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2602,plain,
% 2.81/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_58)) = k3_tmap_1(X1_58,sK1,sK3,X0_58,sK4)
% 2.81/1.00      | m1_pre_topc(X0_58,X1_58) != iProver_top
% 2.81/1.00      | m1_pre_topc(X0_58,sK3) != iProver_top
% 2.81/1.00      | m1_pre_topc(sK3,X1_58) != iProver_top
% 2.81/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v2_struct_0(X1_58) = iProver_top
% 2.81/1.00      | v2_struct_0(sK1) = iProver_top
% 2.81/1.00      | v2_pre_topc(X1_58) != iProver_top
% 2.81/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.81/1.00      | l1_pre_topc(X1_58) != iProver_top
% 2.81/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.81/1.00      inference(equality_resolution,[status(thm)],[c_2332]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_13,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.81/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_382,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 2.81/1.00      | sK4 != X0 ),
% 2.81/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_383,plain,
% 2.81/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.81/1.00      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 2.81/1.00      inference(unflattening,[status(thm)],[c_382]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1188,plain,
% 2.81/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.81/1.00      | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_383]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1770,plain,
% 2.81/1.00      ( k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57)
% 2.81/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1188]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2272,plain,
% 2.81/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1758,c_1770]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2603,plain,
% 2.81/1.00      ( k3_tmap_1(X0_58,sK1,sK3,X1_58,sK4) = k7_relat_1(sK4,u1_struct_0(X1_58))
% 2.81/1.00      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 2.81/1.00      | m1_pre_topc(X1_58,sK3) != iProver_top
% 2.81/1.00      | m1_pre_topc(sK3,X0_58) != iProver_top
% 2.81/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v2_struct_0(X0_58) = iProver_top
% 2.81/1.00      | v2_struct_0(sK1) = iProver_top
% 2.81/1.00      | v2_pre_topc(X0_58) != iProver_top
% 2.81/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.81/1.00      | l1_pre_topc(X0_58) != iProver_top
% 2.81/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_2602,c_2272]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_28,negated_conjecture,
% 2.81/1.00      ( ~ v2_struct_0(sK1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_35,plain,
% 2.81/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_27,negated_conjecture,
% 2.81/1.00      ( v2_pre_topc(sK1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_36,plain,
% 2.81/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_26,negated_conjecture,
% 2.81/1.00      ( l1_pre_topc(sK1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_37,plain,
% 2.81/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2681,plain,
% 2.81/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 2.81/1.00      | v2_struct_0(X0_58) = iProver_top
% 2.81/1.00      | k3_tmap_1(X0_58,sK1,sK3,X1_58,sK4) = k7_relat_1(sK4,u1_struct_0(X1_58))
% 2.81/1.00      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 2.81/1.00      | m1_pre_topc(X1_58,sK3) != iProver_top
% 2.81/1.00      | m1_pre_topc(sK3,X0_58) != iProver_top
% 2.81/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2603,c_35,c_36,c_37,c_44]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2682,plain,
% 2.81/1.00      ( k3_tmap_1(X0_58,sK1,sK3,X1_58,sK4) = k7_relat_1(sK4,u1_struct_0(X1_58))
% 2.81/1.00      | m1_pre_topc(X1_58,X0_58) != iProver_top
% 2.81/1.00      | m1_pre_topc(X1_58,sK3) != iProver_top
% 2.81/1.00      | m1_pre_topc(sK3,X0_58) != iProver_top
% 2.81/1.00      | v2_struct_0(X0_58) = iProver_top
% 2.81/1.00      | v2_pre_topc(X0_58) != iProver_top
% 2.81/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 2.81/1.00      inference(renaming,[status(thm)],[c_2681]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2696,plain,
% 2.81/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 2.81/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 2.81/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 2.81/1.00      | v2_struct_0(sK0) = iProver_top
% 2.81/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.81/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1761,c_2682]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_31,negated_conjecture,
% 2.81/1.00      ( ~ v2_struct_0(sK0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_32,plain,
% 2.81/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_30,negated_conjecture,
% 2.81/1.00      ( v2_pre_topc(sK0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_33,plain,
% 2.81/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_29,negated_conjecture,
% 2.81/1.00      ( l1_pre_topc(sK0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_34,plain,
% 2.81/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_22,negated_conjecture,
% 2.81/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_41,plain,
% 2.81/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_18,negated_conjecture,
% 2.81/1.00      ( m1_pre_topc(sK2,sK3) ),
% 2.81/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_45,plain,
% 2.81/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2812,plain,
% 2.81/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2696,c_32,c_33,c_34,c_41,c_45]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_15,negated_conjecture,
% 2.81/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 2.81/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1204,negated_conjecture,
% 2.81/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2815,plain,
% 2.81/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_2812,c_1204]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3064,plain,
% 2.81/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k10_relat_1(sK4,sK5) ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_2956,c_2815]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5240,plain,
% 2.81/1.00      ( k3_xboole_0(u1_struct_0(sK2),k10_relat_1(sK4,sK5)) != k10_relat_1(sK4,sK5) ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_5236,c_3064]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_0,plain,
% 2.81/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1217,plain,
% 2.81/1.00      ( k3_xboole_0(X0_57,X1_57) = k3_xboole_0(X1_57,X0_57) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_16,negated_conjecture,
% 2.81/1.00      ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1203,negated_conjecture,
% 2.81/1.00      ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1755,plain,
% 2.81/1.00      ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1203]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1,plain,
% 2.81/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.81/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1216,plain,
% 2.81/1.00      ( ~ r1_tarski(X0_57,X1_57) | k3_xboole_0(X0_57,X1_57) = X0_57 ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1743,plain,
% 2.81/1.00      ( k3_xboole_0(X0_57,X1_57) = X0_57
% 2.81/1.00      | r1_tarski(X0_57,X1_57) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2209,plain,
% 2.81/1.00      ( k3_xboole_0(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1755,c_1743]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2211,plain,
% 2.81/1.00      ( k3_xboole_0(u1_struct_0(sK2),k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5)) = k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1217,c_2209]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3065,plain,
% 2.81/1.00      ( k3_xboole_0(u1_struct_0(sK2),k10_relat_1(sK4,sK5)) = k10_relat_1(sK4,sK5) ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_2956,c_2211]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5241,plain,
% 2.81/1.00      ( k10_relat_1(sK4,sK5) != k10_relat_1(sK4,sK5) ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_5240,c_3065]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5242,plain,
% 2.81/1.00      ( $false ),
% 2.81/1.00      inference(equality_resolution_simp,[status(thm)],[c_5241]) ).
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  ------                               Statistics
% 2.81/1.00  
% 2.81/1.00  ------ General
% 2.81/1.00  
% 2.81/1.00  abstr_ref_over_cycles:                  0
% 2.81/1.00  abstr_ref_under_cycles:                 0
% 2.81/1.00  gc_basic_clause_elim:                   0
% 2.81/1.00  forced_gc_time:                         0
% 2.81/1.00  parsing_time:                           0.01
% 2.81/1.00  unif_index_cands_time:                  0.
% 2.81/1.00  unif_index_add_time:                    0.
% 2.81/1.00  orderings_time:                         0.
% 2.81/1.00  out_proof_time:                         0.012
% 2.81/1.00  total_time:                             0.214
% 2.81/1.00  num_of_symbols:                         62
% 2.81/1.00  num_of_terms:                           4837
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing
% 2.81/1.00  
% 2.81/1.00  num_of_splits:                          0
% 2.81/1.00  num_of_split_atoms:                     0
% 2.81/1.00  num_of_reused_defs:                     0
% 2.81/1.00  num_eq_ax_congr_red:                    27
% 2.81/1.00  num_of_sem_filtered_clauses:            1
% 2.81/1.00  num_of_subtypes:                        4
% 2.81/1.00  monotx_restored_types:                  0
% 2.81/1.00  sat_num_of_epr_types:                   0
% 2.81/1.00  sat_num_of_non_cyclic_types:            0
% 2.81/1.00  sat_guarded_non_collapsed_types:        1
% 2.81/1.00  num_pure_diseq_elim:                    0
% 2.81/1.00  simp_replaced_by:                       0
% 2.81/1.00  res_preprocessed:                       159
% 2.81/1.00  prep_upred:                             0
% 2.81/1.00  prep_unflattend:                        18
% 2.81/1.00  smt_new_axioms:                         0
% 2.81/1.00  pred_elim_cands:                        8
% 2.81/1.00  pred_elim:                              2
% 2.81/1.00  pred_elim_cl:                           2
% 2.81/1.00  pred_elim_cycles:                       4
% 2.81/1.00  merged_defs:                            0
% 2.81/1.00  merged_defs_ncl:                        0
% 2.81/1.00  bin_hyper_res:                          0
% 2.81/1.00  prep_cycles:                            4
% 2.81/1.00  pred_elim_time:                         0.016
% 2.81/1.00  splitting_time:                         0.
% 2.81/1.00  sem_filter_time:                        0.
% 2.81/1.00  monotx_time:                            0.
% 2.81/1.00  subtype_inf_time:                       0.001
% 2.81/1.00  
% 2.81/1.00  ------ Problem properties
% 2.81/1.00  
% 2.81/1.00  clauses:                                30
% 2.81/1.00  conjectures:                            15
% 2.81/1.00  epr:                                    11
% 2.81/1.00  horn:                                   29
% 2.81/1.00  ground:                                 15
% 2.81/1.00  unary:                                  16
% 2.81/1.00  binary:                                 8
% 2.81/1.00  lits:                                   61
% 2.81/1.00  lits_eq:                                9
% 2.81/1.00  fd_pure:                                0
% 2.81/1.00  fd_pseudo:                              0
% 2.81/1.00  fd_cond:                                0
% 2.81/1.00  fd_pseudo_cond:                         0
% 2.81/1.00  ac_symbols:                             0
% 2.81/1.00  
% 2.81/1.00  ------ Propositional Solver
% 2.81/1.00  
% 2.81/1.00  prop_solver_calls:                      29
% 2.81/1.00  prop_fast_solver_calls:                 1087
% 2.81/1.00  smt_solver_calls:                       0
% 2.81/1.00  smt_fast_solver_calls:                  0
% 2.81/1.00  prop_num_of_clauses:                    1656
% 2.81/1.00  prop_preprocess_simplified:             6324
% 2.81/1.00  prop_fo_subsumed:                       26
% 2.81/1.00  prop_solver_time:                       0.
% 2.81/1.00  smt_solver_time:                        0.
% 2.81/1.00  smt_fast_solver_time:                   0.
% 2.81/1.00  prop_fast_solver_time:                  0.
% 2.81/1.00  prop_unsat_core_time:                   0.
% 2.81/1.00  
% 2.81/1.00  ------ QBF
% 2.81/1.00  
% 2.81/1.00  qbf_q_res:                              0
% 2.81/1.00  qbf_num_tautologies:                    0
% 2.81/1.00  qbf_prep_cycles:                        0
% 2.81/1.00  
% 2.81/1.00  ------ BMC1
% 2.81/1.00  
% 2.81/1.00  bmc1_current_bound:                     -1
% 2.81/1.00  bmc1_last_solved_bound:                 -1
% 2.81/1.00  bmc1_unsat_core_size:                   -1
% 2.81/1.00  bmc1_unsat_core_parents_size:           -1
% 2.81/1.00  bmc1_merge_next_fun:                    0
% 2.81/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.81/1.00  
% 2.81/1.00  ------ Instantiation
% 2.81/1.00  
% 2.81/1.00  inst_num_of_clauses:                    676
% 2.81/1.00  inst_num_in_passive:                    8
% 2.81/1.00  inst_num_in_active:                     401
% 2.81/1.00  inst_num_in_unprocessed:                268
% 2.81/1.00  inst_num_of_loops:                      420
% 2.81/1.00  inst_num_of_learning_restarts:          0
% 2.81/1.00  inst_num_moves_active_passive:          15
% 2.81/1.00  inst_lit_activity:                      0
% 2.81/1.00  inst_lit_activity_moves:                0
% 2.81/1.00  inst_num_tautologies:                   0
% 2.81/1.00  inst_num_prop_implied:                  0
% 2.81/1.00  inst_num_existing_simplified:           0
% 2.81/1.00  inst_num_eq_res_simplified:             0
% 2.81/1.00  inst_num_child_elim:                    0
% 2.81/1.00  inst_num_of_dismatching_blockings:      148
% 2.81/1.00  inst_num_of_non_proper_insts:           713
% 2.81/1.00  inst_num_of_duplicates:                 0
% 2.81/1.00  inst_inst_num_from_inst_to_res:         0
% 2.81/1.00  inst_dismatching_checking_time:         0.
% 2.81/1.00  
% 2.81/1.00  ------ Resolution
% 2.81/1.00  
% 2.81/1.00  res_num_of_clauses:                     0
% 2.81/1.00  res_num_in_passive:                     0
% 2.81/1.00  res_num_in_active:                      0
% 2.81/1.00  res_num_of_loops:                       163
% 2.81/1.00  res_forward_subset_subsumed:            123
% 2.81/1.00  res_backward_subset_subsumed:           2
% 2.81/1.00  res_forward_subsumed:                   2
% 2.81/1.00  res_backward_subsumed:                  0
% 2.81/1.00  res_forward_subsumption_resolution:     0
% 2.81/1.00  res_backward_subsumption_resolution:    0
% 2.81/1.00  res_clause_to_clause_subsumption:       205
% 2.81/1.00  res_orphan_elimination:                 0
% 2.81/1.00  res_tautology_del:                      116
% 2.81/1.00  res_num_eq_res_simplified:              0
% 2.81/1.00  res_num_sel_changes:                    0
% 2.81/1.00  res_moves_from_active_to_pass:          0
% 2.81/1.00  
% 2.81/1.00  ------ Superposition
% 2.81/1.00  
% 2.81/1.00  sup_time_total:                         0.
% 2.81/1.00  sup_time_generating:                    0.
% 2.81/1.00  sup_time_sim_full:                      0.
% 2.81/1.00  sup_time_sim_immed:                     0.
% 2.81/1.00  
% 2.81/1.00  sup_num_of_clauses:                     83
% 2.81/1.00  sup_num_in_active:                      76
% 2.81/1.00  sup_num_in_passive:                     7
% 2.81/1.00  sup_num_of_loops:                       82
% 2.81/1.00  sup_fw_superposition:                   58
% 2.81/1.00  sup_bw_superposition:                   27
% 2.81/1.00  sup_immediate_simplified:               7
% 2.81/1.00  sup_given_eliminated:                   0
% 2.81/1.00  comparisons_done:                       0
% 2.81/1.00  comparisons_avoided:                    0
% 2.81/1.00  
% 2.81/1.00  ------ Simplifications
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  sim_fw_subset_subsumed:                 0
% 2.81/1.00  sim_bw_subset_subsumed:                 0
% 2.81/1.00  sim_fw_subsumed:                        2
% 2.81/1.00  sim_bw_subsumed:                        0
% 2.81/1.00  sim_fw_subsumption_res:                 0
% 2.81/1.00  sim_bw_subsumption_res:                 0
% 2.81/1.00  sim_tautology_del:                      2
% 2.81/1.00  sim_eq_tautology_del:                   0
% 2.81/1.00  sim_eq_res_simp:                        0
% 2.81/1.00  sim_fw_demodulated:                     1
% 2.81/1.00  sim_bw_demodulated:                     6
% 2.81/1.00  sim_light_normalised:                   6
% 2.81/1.00  sim_joinable_taut:                      0
% 2.81/1.00  sim_joinable_simp:                      0
% 2.81/1.00  sim_ac_normalised:                      0
% 2.81/1.00  sim_smt_subsumption:                    0
% 2.81/1.00  
%------------------------------------------------------------------------------
