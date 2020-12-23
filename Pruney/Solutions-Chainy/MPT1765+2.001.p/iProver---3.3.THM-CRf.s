%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:57 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 794 expanded)
%              Number of clauses        :  110 ( 195 expanded)
%              Number of leaves         :   18 ( 329 expanded)
%              Depth                    :   20
%              Number of atoms          :  748 (9899 expanded)
%              Number of equality atoms :  218 (1012 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ( r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                             => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ( r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
                               => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5),u1_struct_0(X2))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f37,f36,f35,f34,f33,f32])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_529,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1055,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_528,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1056,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_536,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,X0_53,X2_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1049,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,X0_53,X2_55)
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_2121,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1049])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_39,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_41,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_537,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1455,plain,
    ( ~ m1_pre_topc(sK3,X0_55)
    | ~ l1_pre_topc(X0_55)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1546,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_1547,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1546])).

cnf(c_525,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1059,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_539,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1046,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_1814,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1046])).

cnf(c_2778,plain,
    ( m1_pre_topc(X0_55,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_31,c_32,c_33,c_34,c_35,c_38,c_39,c_40,c_41,c_1547,c_1814])).

cnf(c_2779,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2778])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1045,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_1841,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1045])).

cnf(c_1339,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_2673,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1841,c_19,c_17,c_1339])).

cnf(c_2784,plain,
    ( k2_tmap_1(sK3,sK1,sK4,X0_55) = k7_relat_1(sK4,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2779,c_2673])).

cnf(c_2790,plain,
    ( k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1055,c_2784])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_534,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k2_tmap_1(X0_55,X1_55,X0_53,X2_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X0_55)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1051,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_55,X1_55,X0_53,X2_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
    | l1_struct_0(X2_55) != iProver_top
    | l1_struct_0(X1_55) != iProver_top
    | l1_struct_0(X0_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2827,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2790,c_1051])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_62,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_64,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_538,plain,
    ( l1_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1418,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1419,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1418])).

cnf(c_1048,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_1751,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1048])).

cnf(c_1952,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1751,c_32,c_39,c_1547])).

cnf(c_1047,plain,
    ( l1_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_1957,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_1047])).

cnf(c_3302,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2827,c_32,c_35,c_39,c_40,c_41,c_42,c_64,c_1419,c_1547,c_1957])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1044,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_3312,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),X0_53) = k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),X0_53) ),
    inference(superposition,[status(thm)],[c_3302,c_1044])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_523,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1061,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_535,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X2_55,X0_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | v2_struct_0(X3_55)
    | v2_struct_0(X1_55)
    | ~ l1_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1050,plain,
    ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53)
    | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_2494,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1050])).

cnf(c_2866,plain,
    ( l1_pre_topc(X1_55) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2494,c_33,c_34,c_35,c_40,c_41])).

cnf(c_2867,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
    | m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2866])).

cnf(c_2872,plain,
    ( k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X1_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2867,c_2673])).

cnf(c_2883,plain,
    ( k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK0) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_2872])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2948,plain,
    ( m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(X0_55,sK0) != iProver_top
    | k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2883,c_30,c_31,c_32])).

cnf(c_2949,plain,
    ( k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55))
    | m1_pre_topc(X0_55,sK0) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2948])).

cnf(c_2958,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_2949])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3087,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2958,c_43])).

cnf(c_1681,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k10_relat_1(sK4,X0_53) ),
    inference(superposition,[status(thm)],[c_1056,c_1044])).

cnf(c_13,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_531,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2036,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k10_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_1681,c_531])).

cnf(c_3090,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k10_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3087,c_2036])).

cnf(c_3479,plain,
    ( k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k10_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3312,c_3090])).

cnf(c_4,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_303,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k10_relat_1(X0,X1)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
    | u1_struct_0(sK2) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_304,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k10_relat_1(X0,X1)
    | k10_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),X1) = k10_relat_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_515,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k10_relat_1(X0_53,X1_53)
    | k10_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),X1_53) = k10_relat_1(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_304])).

cnf(c_1525,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k10_relat_1(sK4,sK5)
    | k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k10_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_542,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1490,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1308,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1423,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_1334,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k10_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_1408,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k10_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3479,c_1525,c_1490,c_1423,c_1408,c_17,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:50:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.36/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/1.00  
% 2.36/1.00  ------  iProver source info
% 2.36/1.00  
% 2.36/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.36/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/1.00  git: non_committed_changes: false
% 2.36/1.00  git: last_make_outside_of_git: false
% 2.36/1.00  
% 2.36/1.00  ------ 
% 2.36/1.00  
% 2.36/1.00  ------ Input Options
% 2.36/1.00  
% 2.36/1.00  --out_options                           all
% 2.36/1.00  --tptp_safe_out                         true
% 2.36/1.00  --problem_path                          ""
% 2.36/1.00  --include_path                          ""
% 2.36/1.00  --clausifier                            res/vclausify_rel
% 2.36/1.00  --clausifier_options                    --mode clausify
% 2.36/1.00  --stdin                                 false
% 2.36/1.00  --stats_out                             all
% 2.36/1.00  
% 2.36/1.00  ------ General Options
% 2.36/1.00  
% 2.36/1.00  --fof                                   false
% 2.36/1.00  --time_out_real                         305.
% 2.36/1.00  --time_out_virtual                      -1.
% 2.36/1.00  --symbol_type_check                     false
% 2.36/1.00  --clausify_out                          false
% 2.36/1.00  --sig_cnt_out                           false
% 2.36/1.00  --trig_cnt_out                          false
% 2.36/1.00  --trig_cnt_out_tolerance                1.
% 2.36/1.00  --trig_cnt_out_sk_spl                   false
% 2.36/1.00  --abstr_cl_out                          false
% 2.36/1.00  
% 2.36/1.00  ------ Global Options
% 2.36/1.00  
% 2.36/1.00  --schedule                              default
% 2.36/1.00  --add_important_lit                     false
% 2.36/1.00  --prop_solver_per_cl                    1000
% 2.36/1.00  --min_unsat_core                        false
% 2.36/1.00  --soft_assumptions                      false
% 2.36/1.00  --soft_lemma_size                       3
% 2.36/1.00  --prop_impl_unit_size                   0
% 2.36/1.00  --prop_impl_unit                        []
% 2.36/1.00  --share_sel_clauses                     true
% 2.36/1.00  --reset_solvers                         false
% 2.36/1.00  --bc_imp_inh                            [conj_cone]
% 2.36/1.00  --conj_cone_tolerance                   3.
% 2.36/1.00  --extra_neg_conj                        none
% 2.36/1.00  --large_theory_mode                     true
% 2.36/1.00  --prolific_symb_bound                   200
% 2.36/1.00  --lt_threshold                          2000
% 2.36/1.00  --clause_weak_htbl                      true
% 2.36/1.00  --gc_record_bc_elim                     false
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing Options
% 2.36/1.00  
% 2.36/1.00  --preprocessing_flag                    true
% 2.36/1.00  --time_out_prep_mult                    0.1
% 2.36/1.00  --splitting_mode                        input
% 2.36/1.00  --splitting_grd                         true
% 2.36/1.00  --splitting_cvd                         false
% 2.36/1.00  --splitting_cvd_svl                     false
% 2.36/1.00  --splitting_nvd                         32
% 2.36/1.00  --sub_typing                            true
% 2.36/1.00  --prep_gs_sim                           true
% 2.36/1.00  --prep_unflatten                        true
% 2.36/1.00  --prep_res_sim                          true
% 2.36/1.00  --prep_upred                            true
% 2.36/1.00  --prep_sem_filter                       exhaustive
% 2.36/1.00  --prep_sem_filter_out                   false
% 2.36/1.00  --pred_elim                             true
% 2.36/1.00  --res_sim_input                         true
% 2.36/1.00  --eq_ax_congr_red                       true
% 2.36/1.00  --pure_diseq_elim                       true
% 2.36/1.00  --brand_transform                       false
% 2.36/1.00  --non_eq_to_eq                          false
% 2.36/1.00  --prep_def_merge                        true
% 2.36/1.00  --prep_def_merge_prop_impl              false
% 2.36/1.00  --prep_def_merge_mbd                    true
% 2.36/1.00  --prep_def_merge_tr_red                 false
% 2.36/1.00  --prep_def_merge_tr_cl                  false
% 2.36/1.00  --smt_preprocessing                     true
% 2.36/1.00  --smt_ac_axioms                         fast
% 2.36/1.00  --preprocessed_out                      false
% 2.36/1.00  --preprocessed_stats                    false
% 2.36/1.00  
% 2.36/1.00  ------ Abstraction refinement Options
% 2.36/1.00  
% 2.36/1.00  --abstr_ref                             []
% 2.36/1.00  --abstr_ref_prep                        false
% 2.36/1.00  --abstr_ref_until_sat                   false
% 2.36/1.00  --abstr_ref_sig_restrict                funpre
% 2.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/1.00  --abstr_ref_under                       []
% 2.36/1.00  
% 2.36/1.00  ------ SAT Options
% 2.36/1.00  
% 2.36/1.00  --sat_mode                              false
% 2.36/1.00  --sat_fm_restart_options                ""
% 2.36/1.00  --sat_gr_def                            false
% 2.36/1.00  --sat_epr_types                         true
% 2.36/1.00  --sat_non_cyclic_types                  false
% 2.36/1.00  --sat_finite_models                     false
% 2.36/1.00  --sat_fm_lemmas                         false
% 2.36/1.00  --sat_fm_prep                           false
% 2.36/1.00  --sat_fm_uc_incr                        true
% 2.36/1.00  --sat_out_model                         small
% 2.36/1.00  --sat_out_clauses                       false
% 2.36/1.00  
% 2.36/1.00  ------ QBF Options
% 2.36/1.00  
% 2.36/1.00  --qbf_mode                              false
% 2.36/1.00  --qbf_elim_univ                         false
% 2.36/1.00  --qbf_dom_inst                          none
% 2.36/1.00  --qbf_dom_pre_inst                      false
% 2.36/1.00  --qbf_sk_in                             false
% 2.36/1.00  --qbf_pred_elim                         true
% 2.36/1.00  --qbf_split                             512
% 2.36/1.00  
% 2.36/1.00  ------ BMC1 Options
% 2.36/1.00  
% 2.36/1.00  --bmc1_incremental                      false
% 2.36/1.00  --bmc1_axioms                           reachable_all
% 2.36/1.00  --bmc1_min_bound                        0
% 2.36/1.00  --bmc1_max_bound                        -1
% 2.36/1.00  --bmc1_max_bound_default                -1
% 2.36/1.00  --bmc1_symbol_reachability              true
% 2.36/1.00  --bmc1_property_lemmas                  false
% 2.36/1.00  --bmc1_k_induction                      false
% 2.36/1.00  --bmc1_non_equiv_states                 false
% 2.36/1.00  --bmc1_deadlock                         false
% 2.36/1.00  --bmc1_ucm                              false
% 2.36/1.00  --bmc1_add_unsat_core                   none
% 2.36/1.00  --bmc1_unsat_core_children              false
% 2.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.00  --bmc1_out_stat                         full
% 2.36/1.00  --bmc1_ground_init                      false
% 2.36/1.00  --bmc1_pre_inst_next_state              false
% 2.36/1.00  --bmc1_pre_inst_state                   false
% 2.36/1.00  --bmc1_pre_inst_reach_state             false
% 2.36/1.00  --bmc1_out_unsat_core                   false
% 2.36/1.00  --bmc1_aig_witness_out                  false
% 2.36/1.00  --bmc1_verbose                          false
% 2.36/1.00  --bmc1_dump_clauses_tptp                false
% 2.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.00  --bmc1_dump_file                        -
% 2.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.00  --bmc1_ucm_extend_mode                  1
% 2.36/1.00  --bmc1_ucm_init_mode                    2
% 2.36/1.00  --bmc1_ucm_cone_mode                    none
% 2.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.00  --bmc1_ucm_relax_model                  4
% 2.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.00  --bmc1_ucm_layered_model                none
% 2.36/1.00  --bmc1_ucm_max_lemma_size               10
% 2.36/1.00  
% 2.36/1.00  ------ AIG Options
% 2.36/1.00  
% 2.36/1.00  --aig_mode                              false
% 2.36/1.00  
% 2.36/1.00  ------ Instantiation Options
% 2.36/1.00  
% 2.36/1.00  --instantiation_flag                    true
% 2.36/1.00  --inst_sos_flag                         false
% 2.36/1.00  --inst_sos_phase                        true
% 2.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel_side                     num_symb
% 2.36/1.00  --inst_solver_per_active                1400
% 2.36/1.00  --inst_solver_calls_frac                1.
% 2.36/1.00  --inst_passive_queue_type               priority_queues
% 2.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.00  --inst_passive_queues_freq              [25;2]
% 2.36/1.00  --inst_dismatching                      true
% 2.36/1.00  --inst_eager_unprocessed_to_passive     true
% 2.36/1.00  --inst_prop_sim_given                   true
% 2.36/1.00  --inst_prop_sim_new                     false
% 2.36/1.00  --inst_subs_new                         false
% 2.36/1.00  --inst_eq_res_simp                      false
% 2.36/1.00  --inst_subs_given                       false
% 2.36/1.00  --inst_orphan_elimination               true
% 2.36/1.00  --inst_learning_loop_flag               true
% 2.36/1.00  --inst_learning_start                   3000
% 2.36/1.00  --inst_learning_factor                  2
% 2.36/1.00  --inst_start_prop_sim_after_learn       3
% 2.36/1.00  --inst_sel_renew                        solver
% 2.36/1.00  --inst_lit_activity_flag                true
% 2.36/1.00  --inst_restr_to_given                   false
% 2.36/1.00  --inst_activity_threshold               500
% 2.36/1.00  --inst_out_proof                        true
% 2.36/1.00  
% 2.36/1.00  ------ Resolution Options
% 2.36/1.00  
% 2.36/1.00  --resolution_flag                       true
% 2.36/1.00  --res_lit_sel                           adaptive
% 2.36/1.00  --res_lit_sel_side                      none
% 2.36/1.00  --res_ordering                          kbo
% 2.36/1.00  --res_to_prop_solver                    active
% 2.36/1.00  --res_prop_simpl_new                    false
% 2.36/1.00  --res_prop_simpl_given                  true
% 2.36/1.00  --res_passive_queue_type                priority_queues
% 2.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.00  --res_passive_queues_freq               [15;5]
% 2.36/1.00  --res_forward_subs                      full
% 2.36/1.00  --res_backward_subs                     full
% 2.36/1.00  --res_forward_subs_resolution           true
% 2.36/1.00  --res_backward_subs_resolution          true
% 2.36/1.00  --res_orphan_elimination                true
% 2.36/1.00  --res_time_limit                        2.
% 2.36/1.00  --res_out_proof                         true
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Options
% 2.36/1.00  
% 2.36/1.00  --superposition_flag                    true
% 2.36/1.00  --sup_passive_queue_type                priority_queues
% 2.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.00  --demod_completeness_check              fast
% 2.36/1.00  --demod_use_ground                      true
% 2.36/1.00  --sup_to_prop_solver                    passive
% 2.36/1.00  --sup_prop_simpl_new                    true
% 2.36/1.00  --sup_prop_simpl_given                  true
% 2.36/1.00  --sup_fun_splitting                     false
% 2.36/1.00  --sup_smt_interval                      50000
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Simplification Setup
% 2.36/1.00  
% 2.36/1.00  --sup_indices_passive                   []
% 2.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_full_bw                           [BwDemod]
% 2.36/1.00  --sup_immed_triv                        [TrivRules]
% 2.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_immed_bw_main                     []
% 2.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  
% 2.36/1.00  ------ Combination Options
% 2.36/1.00  
% 2.36/1.00  --comb_res_mult                         3
% 2.36/1.00  --comb_sup_mult                         2
% 2.36/1.00  --comb_inst_mult                        10
% 2.36/1.00  
% 2.36/1.00  ------ Debug Options
% 2.36/1.00  
% 2.36/1.00  --dbg_backtrace                         false
% 2.36/1.00  --dbg_dump_prop_clauses                 false
% 2.36/1.00  --dbg_dump_prop_clauses_file            -
% 2.36/1.00  --dbg_out_stat                          false
% 2.36/1.00  ------ Parsing...
% 2.36/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/1.00  ------ Proving...
% 2.36/1.00  ------ Problem Properties 
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  clauses                                 29
% 2.36/1.00  conjectures                             16
% 2.36/1.00  EPR                                     15
% 2.36/1.00  Horn                                    27
% 2.36/1.00  unary                                   17
% 2.36/1.00  binary                                  2
% 2.36/1.00  lits                                    83
% 2.36/1.00  lits eq                                 7
% 2.36/1.00  fd_pure                                 0
% 2.36/1.00  fd_pseudo                               0
% 2.36/1.00  fd_cond                                 0
% 2.36/1.00  fd_pseudo_cond                          0
% 2.36/1.00  AC symbols                              0
% 2.36/1.00  
% 2.36/1.00  ------ Schedule dynamic 5 is on 
% 2.36/1.00  
% 2.36/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  ------ 
% 2.36/1.00  Current options:
% 2.36/1.00  ------ 
% 2.36/1.00  
% 2.36/1.00  ------ Input Options
% 2.36/1.00  
% 2.36/1.00  --out_options                           all
% 2.36/1.00  --tptp_safe_out                         true
% 2.36/1.00  --problem_path                          ""
% 2.36/1.00  --include_path                          ""
% 2.36/1.00  --clausifier                            res/vclausify_rel
% 2.36/1.00  --clausifier_options                    --mode clausify
% 2.36/1.00  --stdin                                 false
% 2.36/1.00  --stats_out                             all
% 2.36/1.00  
% 2.36/1.00  ------ General Options
% 2.36/1.00  
% 2.36/1.00  --fof                                   false
% 2.36/1.00  --time_out_real                         305.
% 2.36/1.00  --time_out_virtual                      -1.
% 2.36/1.00  --symbol_type_check                     false
% 2.36/1.00  --clausify_out                          false
% 2.36/1.00  --sig_cnt_out                           false
% 2.36/1.00  --trig_cnt_out                          false
% 2.36/1.00  --trig_cnt_out_tolerance                1.
% 2.36/1.00  --trig_cnt_out_sk_spl                   false
% 2.36/1.00  --abstr_cl_out                          false
% 2.36/1.00  
% 2.36/1.00  ------ Global Options
% 2.36/1.00  
% 2.36/1.00  --schedule                              default
% 2.36/1.00  --add_important_lit                     false
% 2.36/1.00  --prop_solver_per_cl                    1000
% 2.36/1.00  --min_unsat_core                        false
% 2.36/1.00  --soft_assumptions                      false
% 2.36/1.00  --soft_lemma_size                       3
% 2.36/1.00  --prop_impl_unit_size                   0
% 2.36/1.00  --prop_impl_unit                        []
% 2.36/1.00  --share_sel_clauses                     true
% 2.36/1.00  --reset_solvers                         false
% 2.36/1.00  --bc_imp_inh                            [conj_cone]
% 2.36/1.00  --conj_cone_tolerance                   3.
% 2.36/1.00  --extra_neg_conj                        none
% 2.36/1.00  --large_theory_mode                     true
% 2.36/1.00  --prolific_symb_bound                   200
% 2.36/1.00  --lt_threshold                          2000
% 2.36/1.00  --clause_weak_htbl                      true
% 2.36/1.00  --gc_record_bc_elim                     false
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing Options
% 2.36/1.00  
% 2.36/1.00  --preprocessing_flag                    true
% 2.36/1.00  --time_out_prep_mult                    0.1
% 2.36/1.00  --splitting_mode                        input
% 2.36/1.00  --splitting_grd                         true
% 2.36/1.00  --splitting_cvd                         false
% 2.36/1.00  --splitting_cvd_svl                     false
% 2.36/1.00  --splitting_nvd                         32
% 2.36/1.00  --sub_typing                            true
% 2.36/1.00  --prep_gs_sim                           true
% 2.36/1.00  --prep_unflatten                        true
% 2.36/1.00  --prep_res_sim                          true
% 2.36/1.00  --prep_upred                            true
% 2.36/1.00  --prep_sem_filter                       exhaustive
% 2.36/1.00  --prep_sem_filter_out                   false
% 2.36/1.00  --pred_elim                             true
% 2.36/1.00  --res_sim_input                         true
% 2.36/1.00  --eq_ax_congr_red                       true
% 2.36/1.00  --pure_diseq_elim                       true
% 2.36/1.00  --brand_transform                       false
% 2.36/1.00  --non_eq_to_eq                          false
% 2.36/1.00  --prep_def_merge                        true
% 2.36/1.00  --prep_def_merge_prop_impl              false
% 2.36/1.00  --prep_def_merge_mbd                    true
% 2.36/1.00  --prep_def_merge_tr_red                 false
% 2.36/1.00  --prep_def_merge_tr_cl                  false
% 2.36/1.00  --smt_preprocessing                     true
% 2.36/1.00  --smt_ac_axioms                         fast
% 2.36/1.00  --preprocessed_out                      false
% 2.36/1.00  --preprocessed_stats                    false
% 2.36/1.00  
% 2.36/1.00  ------ Abstraction refinement Options
% 2.36/1.00  
% 2.36/1.00  --abstr_ref                             []
% 2.36/1.00  --abstr_ref_prep                        false
% 2.36/1.00  --abstr_ref_until_sat                   false
% 2.36/1.00  --abstr_ref_sig_restrict                funpre
% 2.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/1.00  --abstr_ref_under                       []
% 2.36/1.00  
% 2.36/1.00  ------ SAT Options
% 2.36/1.00  
% 2.36/1.00  --sat_mode                              false
% 2.36/1.00  --sat_fm_restart_options                ""
% 2.36/1.00  --sat_gr_def                            false
% 2.36/1.00  --sat_epr_types                         true
% 2.36/1.00  --sat_non_cyclic_types                  false
% 2.36/1.00  --sat_finite_models                     false
% 2.36/1.00  --sat_fm_lemmas                         false
% 2.36/1.00  --sat_fm_prep                           false
% 2.36/1.00  --sat_fm_uc_incr                        true
% 2.36/1.00  --sat_out_model                         small
% 2.36/1.00  --sat_out_clauses                       false
% 2.36/1.00  
% 2.36/1.00  ------ QBF Options
% 2.36/1.00  
% 2.36/1.00  --qbf_mode                              false
% 2.36/1.00  --qbf_elim_univ                         false
% 2.36/1.00  --qbf_dom_inst                          none
% 2.36/1.00  --qbf_dom_pre_inst                      false
% 2.36/1.00  --qbf_sk_in                             false
% 2.36/1.00  --qbf_pred_elim                         true
% 2.36/1.00  --qbf_split                             512
% 2.36/1.00  
% 2.36/1.00  ------ BMC1 Options
% 2.36/1.00  
% 2.36/1.00  --bmc1_incremental                      false
% 2.36/1.00  --bmc1_axioms                           reachable_all
% 2.36/1.00  --bmc1_min_bound                        0
% 2.36/1.00  --bmc1_max_bound                        -1
% 2.36/1.00  --bmc1_max_bound_default                -1
% 2.36/1.00  --bmc1_symbol_reachability              true
% 2.36/1.00  --bmc1_property_lemmas                  false
% 2.36/1.00  --bmc1_k_induction                      false
% 2.36/1.00  --bmc1_non_equiv_states                 false
% 2.36/1.00  --bmc1_deadlock                         false
% 2.36/1.00  --bmc1_ucm                              false
% 2.36/1.00  --bmc1_add_unsat_core                   none
% 2.36/1.00  --bmc1_unsat_core_children              false
% 2.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.00  --bmc1_out_stat                         full
% 2.36/1.00  --bmc1_ground_init                      false
% 2.36/1.00  --bmc1_pre_inst_next_state              false
% 2.36/1.00  --bmc1_pre_inst_state                   false
% 2.36/1.00  --bmc1_pre_inst_reach_state             false
% 2.36/1.00  --bmc1_out_unsat_core                   false
% 2.36/1.00  --bmc1_aig_witness_out                  false
% 2.36/1.00  --bmc1_verbose                          false
% 2.36/1.00  --bmc1_dump_clauses_tptp                false
% 2.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.00  --bmc1_dump_file                        -
% 2.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.00  --bmc1_ucm_extend_mode                  1
% 2.36/1.00  --bmc1_ucm_init_mode                    2
% 2.36/1.00  --bmc1_ucm_cone_mode                    none
% 2.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.00  --bmc1_ucm_relax_model                  4
% 2.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.00  --bmc1_ucm_layered_model                none
% 2.36/1.00  --bmc1_ucm_max_lemma_size               10
% 2.36/1.00  
% 2.36/1.00  ------ AIG Options
% 2.36/1.00  
% 2.36/1.00  --aig_mode                              false
% 2.36/1.00  
% 2.36/1.00  ------ Instantiation Options
% 2.36/1.00  
% 2.36/1.00  --instantiation_flag                    true
% 2.36/1.00  --inst_sos_flag                         false
% 2.36/1.00  --inst_sos_phase                        true
% 2.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel_side                     none
% 2.36/1.00  --inst_solver_per_active                1400
% 2.36/1.00  --inst_solver_calls_frac                1.
% 2.36/1.00  --inst_passive_queue_type               priority_queues
% 2.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.00  --inst_passive_queues_freq              [25;2]
% 2.36/1.00  --inst_dismatching                      true
% 2.36/1.00  --inst_eager_unprocessed_to_passive     true
% 2.36/1.00  --inst_prop_sim_given                   true
% 2.36/1.00  --inst_prop_sim_new                     false
% 2.36/1.00  --inst_subs_new                         false
% 2.36/1.00  --inst_eq_res_simp                      false
% 2.36/1.00  --inst_subs_given                       false
% 2.36/1.00  --inst_orphan_elimination               true
% 2.36/1.00  --inst_learning_loop_flag               true
% 2.36/1.00  --inst_learning_start                   3000
% 2.36/1.00  --inst_learning_factor                  2
% 2.36/1.00  --inst_start_prop_sim_after_learn       3
% 2.36/1.00  --inst_sel_renew                        solver
% 2.36/1.00  --inst_lit_activity_flag                true
% 2.36/1.00  --inst_restr_to_given                   false
% 2.36/1.00  --inst_activity_threshold               500
% 2.36/1.00  --inst_out_proof                        true
% 2.36/1.00  
% 2.36/1.00  ------ Resolution Options
% 2.36/1.00  
% 2.36/1.00  --resolution_flag                       false
% 2.36/1.00  --res_lit_sel                           adaptive
% 2.36/1.00  --res_lit_sel_side                      none
% 2.36/1.00  --res_ordering                          kbo
% 2.36/1.00  --res_to_prop_solver                    active
% 2.36/1.00  --res_prop_simpl_new                    false
% 2.36/1.00  --res_prop_simpl_given                  true
% 2.36/1.00  --res_passive_queue_type                priority_queues
% 2.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.00  --res_passive_queues_freq               [15;5]
% 2.36/1.00  --res_forward_subs                      full
% 2.36/1.00  --res_backward_subs                     full
% 2.36/1.00  --res_forward_subs_resolution           true
% 2.36/1.00  --res_backward_subs_resolution          true
% 2.36/1.00  --res_orphan_elimination                true
% 2.36/1.00  --res_time_limit                        2.
% 2.36/1.00  --res_out_proof                         true
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Options
% 2.36/1.00  
% 2.36/1.00  --superposition_flag                    true
% 2.36/1.00  --sup_passive_queue_type                priority_queues
% 2.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.00  --demod_completeness_check              fast
% 2.36/1.00  --demod_use_ground                      true
% 2.36/1.00  --sup_to_prop_solver                    passive
% 2.36/1.00  --sup_prop_simpl_new                    true
% 2.36/1.00  --sup_prop_simpl_given                  true
% 2.36/1.00  --sup_fun_splitting                     false
% 2.36/1.00  --sup_smt_interval                      50000
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Simplification Setup
% 2.36/1.00  
% 2.36/1.00  --sup_indices_passive                   []
% 2.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_full_bw                           [BwDemod]
% 2.36/1.00  --sup_immed_triv                        [TrivRules]
% 2.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_immed_bw_main                     []
% 2.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  
% 2.36/1.00  ------ Combination Options
% 2.36/1.00  
% 2.36/1.00  --comb_res_mult                         3
% 2.36/1.00  --comb_sup_mult                         2
% 2.36/1.00  --comb_inst_mult                        10
% 2.36/1.00  
% 2.36/1.00  ------ Debug Options
% 2.36/1.00  
% 2.36/1.00  --dbg_backtrace                         false
% 2.36/1.00  --dbg_dump_prop_clauses                 false
% 2.36/1.00  --dbg_dump_prop_clauses_file            -
% 2.36/1.00  --dbg_out_stat                          false
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  ------ Proving...
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  % SZS status Theorem for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  fof(f12,conjecture,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f13,negated_conjecture,(
% 2.36/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.36/1.00    inference(negated_conjecture,[],[f12])).
% 2.36/1.00  
% 2.36/1.00  fof(f30,plain,(
% 2.36/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f13])).
% 2.36/1.00  
% 2.36/1.00  fof(f31,plain,(
% 2.36/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f30])).
% 2.36/1.00  
% 2.36/1.00  fof(f37,plain,(
% 2.36/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5),u1_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f36,plain,(
% 2.36/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f35,plain,(
% 2.36/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f34,plain,(
% 2.36/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f33,plain,(
% 2.36/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f32,plain,(
% 2.36/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(k8_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5),u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f38,plain,(
% 2.36/1.00    (((((k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f37,f36,f35,f34,f33,f32])).
% 2.36/1.00  
% 2.36/1.00  fof(f65,plain,(
% 2.36/1.00    m1_pre_topc(sK2,sK3)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f64,plain,(
% 2.36/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f9,axiom,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f24,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f9])).
% 2.36/1.00  
% 2.36/1.00  fof(f25,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f24])).
% 2.36/1.00  
% 2.36/1.00  fof(f47,plain,(
% 2.36/1.00    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f25])).
% 2.36/1.00  
% 2.36/1.00  fof(f53,plain,(
% 2.36/1.00    v2_pre_topc(sK0)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f54,plain,(
% 2.36/1.00    l1_pre_topc(sK0)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f55,plain,(
% 2.36/1.00    ~v2_struct_0(sK1)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f56,plain,(
% 2.36/1.00    v2_pre_topc(sK1)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f57,plain,(
% 2.36/1.00    l1_pre_topc(sK1)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f60,plain,(
% 2.36/1.00    ~v2_struct_0(sK3)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f61,plain,(
% 2.36/1.00    m1_pre_topc(sK3,sK0)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f62,plain,(
% 2.36/1.00    v1_funct_1(sK4)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f63,plain,(
% 2.36/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f8,axiom,(
% 2.36/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f23,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f8])).
% 2.36/1.00  
% 2.36/1.00  fof(f46,plain,(
% 2.36/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f23])).
% 2.36/1.00  
% 2.36/1.00  fof(f6,axiom,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f20,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f6])).
% 2.36/1.00  
% 2.36/1.00  fof(f21,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/1.00    inference(flattening,[],[f20])).
% 2.36/1.00  
% 2.36/1.00  fof(f44,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f21])).
% 2.36/1.00  
% 2.36/1.00  fof(f4,axiom,(
% 2.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f16,plain,(
% 2.36/1.00    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.36/1.00    inference(ennf_transformation,[],[f4])).
% 2.36/1.00  
% 2.36/1.00  fof(f17,plain,(
% 2.36/1.00    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.36/1.00    inference(flattening,[],[f16])).
% 2.36/1.00  
% 2.36/1.00  fof(f42,plain,(
% 2.36/1.00    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f17])).
% 2.36/1.00  
% 2.36/1.00  fof(f11,axiom,(
% 2.36/1.00    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f28,plain,(
% 2.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f11])).
% 2.36/1.00  
% 2.36/1.00  fof(f29,plain,(
% 2.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f28])).
% 2.36/1.00  
% 2.36/1.00  fof(f51,plain,(
% 2.36/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f29])).
% 2.36/1.00  
% 2.36/1.00  fof(f7,axiom,(
% 2.36/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f22,plain,(
% 2.36/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f7])).
% 2.36/1.00  
% 2.36/1.00  fof(f45,plain,(
% 2.36/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f22])).
% 2.36/1.00  
% 2.36/1.00  fof(f3,axiom,(
% 2.36/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f15,plain,(
% 2.36/1.00    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/1.00    inference(ennf_transformation,[],[f3])).
% 2.36/1.00  
% 2.36/1.00  fof(f41,plain,(
% 2.36/1.00    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f15])).
% 2.36/1.00  
% 2.36/1.00  fof(f59,plain,(
% 2.36/1.00    m1_pre_topc(sK2,sK0)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f10,axiom,(
% 2.36/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f26,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f10])).
% 2.36/1.00  
% 2.36/1.00  fof(f27,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.36/1.00    inference(flattening,[],[f26])).
% 2.36/1.00  
% 2.36/1.00  fof(f48,plain,(
% 2.36/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f27])).
% 2.36/1.00  
% 2.36/1.00  fof(f52,plain,(
% 2.36/1.00    ~v2_struct_0(sK0)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f68,plain,(
% 2.36/1.00    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f5,axiom,(
% 2.36/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f18,plain,(
% 2.36/1.00    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f5])).
% 2.36/1.00  
% 2.36/1.00  fof(f19,plain,(
% 2.36/1.00    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.36/1.00    inference(flattening,[],[f18])).
% 2.36/1.00  
% 2.36/1.00  fof(f43,plain,(
% 2.36/1.00    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f19])).
% 2.36/1.00  
% 2.36/1.00  fof(f67,plain,(
% 2.36/1.00    r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2))),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f2,axiom,(
% 2.36/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f40,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f2])).
% 2.36/1.00  
% 2.36/1.00  fof(f1,axiom,(
% 2.36/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.36/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f14,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f1])).
% 2.36/1.00  
% 2.36/1.00  fof(f39,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f14])).
% 2.36/1.00  
% 2.36/1.00  cnf(c_16,negated_conjecture,
% 2.36/1.00      ( m1_pre_topc(sK2,sK3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_529,negated_conjecture,
% 2.36/1.00      ( m1_pre_topc(sK2,sK3) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1055,plain,
% 2.36/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_17,negated_conjecture,
% 2.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.36/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_528,negated_conjecture,
% 2.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1056,plain,
% 2.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_8,plain,
% 2.36/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.36/1.00      | ~ m1_pre_topc(X3,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.36/1.00      | v2_struct_0(X1)
% 2.36/1.00      | v2_struct_0(X2)
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | ~ l1_pre_topc(X2)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | ~ v2_pre_topc(X2)
% 2.36/1.00      | ~ v1_funct_1(X0)
% 2.36/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_536,plain,
% 2.36/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.36/1.00      | ~ m1_pre_topc(X2_55,X0_55)
% 2.36/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.36/1.00      | v2_struct_0(X1_55)
% 2.36/1.00      | v2_struct_0(X0_55)
% 2.36/1.00      | ~ l1_pre_topc(X1_55)
% 2.36/1.00      | ~ l1_pre_topc(X0_55)
% 2.36/1.00      | ~ v2_pre_topc(X1_55)
% 2.36/1.00      | ~ v2_pre_topc(X0_55)
% 2.36/1.00      | ~ v1_funct_1(X0_53)
% 2.36/1.00      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,X0_53,X2_55) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1049,plain,
% 2.36/1.00      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,u1_struct_0(X2_55)) = k2_tmap_1(X0_55,X1_55,X0_53,X2_55)
% 2.36/1.00      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 2.36/1.00      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 2.36/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.36/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.36/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.36/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(X0_55) != iProver_top
% 2.36/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2121,plain,
% 2.36/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
% 2.36/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.36/1.00      | v2_struct_0(sK1) = iProver_top
% 2.36/1.00      | v2_struct_0(sK3) = iProver_top
% 2.36/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.36/1.00      | l1_pre_topc(sK3) != iProver_top
% 2.36/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.36/1.00      | v2_pre_topc(sK3) != iProver_top
% 2.36/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1056,c_1049]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_28,negated_conjecture,
% 2.36/1.00      ( v2_pre_topc(sK0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_31,plain,
% 2.36/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_27,negated_conjecture,
% 2.36/1.00      ( l1_pre_topc(sK0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_32,plain,
% 2.36/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_26,negated_conjecture,
% 2.36/1.00      ( ~ v2_struct_0(sK1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_33,plain,
% 2.36/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_25,negated_conjecture,
% 2.36/1.00      ( v2_pre_topc(sK1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_34,plain,
% 2.36/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_24,negated_conjecture,
% 2.36/1.00      ( l1_pre_topc(sK1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_35,plain,
% 2.36/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_21,negated_conjecture,
% 2.36/1.00      ( ~ v2_struct_0(sK3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_38,plain,
% 2.36/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_20,negated_conjecture,
% 2.36/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_39,plain,
% 2.36/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_19,negated_conjecture,
% 2.36/1.00      ( v1_funct_1(sK4) ),
% 2.36/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_40,plain,
% 2.36/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_18,negated_conjecture,
% 2.36/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_41,plain,
% 2.36/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_7,plain,
% 2.36/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_537,plain,
% 2.36/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.36/1.00      | ~ l1_pre_topc(X1_55)
% 2.36/1.00      | l1_pre_topc(X0_55) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1455,plain,
% 2.36/1.00      ( ~ m1_pre_topc(sK3,X0_55)
% 2.36/1.00      | ~ l1_pre_topc(X0_55)
% 2.36/1.00      | l1_pre_topc(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_537]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1546,plain,
% 2.36/1.00      ( ~ m1_pre_topc(sK3,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1455]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1547,plain,
% 2.36/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.36/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.36/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1546]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_525,negated_conjecture,
% 2.36/1.00      ( m1_pre_topc(sK3,sK0) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1059,plain,
% 2.36/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_5,plain,
% 2.36/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.36/1.00      | ~ l1_pre_topc(X1)
% 2.36/1.00      | ~ v2_pre_topc(X1)
% 2.36/1.00      | v2_pre_topc(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_539,plain,
% 2.36/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.36/1.00      | ~ l1_pre_topc(X1_55)
% 2.36/1.00      | ~ v2_pre_topc(X1_55)
% 2.36/1.00      | v2_pre_topc(X0_55) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1046,plain,
% 2.36/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.36/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(X0_55) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1814,plain,
% 2.36/1.00      ( l1_pre_topc(sK0) != iProver_top
% 2.36/1.00      | v2_pre_topc(sK0) != iProver_top
% 2.36/1.00      | v2_pre_topc(sK3) = iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1059,c_1046]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2778,plain,
% 2.36/1.00      ( m1_pre_topc(X0_55,sK3) != iProver_top
% 2.36/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_2121,c_31,c_32,c_33,c_34,c_35,c_38,c_39,c_40,c_41,
% 2.36/1.00                 c_1547,c_1814]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2779,plain,
% 2.36/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k2_tmap_1(sK3,sK1,sK4,X0_55)
% 2.36/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 2.36/1.00      inference(renaming,[status(thm)],[c_2778]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/1.00      | ~ v1_funct_1(X0)
% 2.36/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_540,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.36/1.00      | ~ v1_funct_1(X0_53)
% 2.36/1.00      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1045,plain,
% 2.36/1.00      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 2.36/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.36/1.00      | v1_funct_1(X2_53) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1841,plain,
% 2.36/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 2.36/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1056,c_1045]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1339,plain,
% 2.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.36/1.00      | ~ v1_funct_1(sK4)
% 2.36/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_540]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2673,plain,
% 2.36/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_1841,c_19,c_17,c_1339]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2784,plain,
% 2.36/1.00      ( k2_tmap_1(sK3,sK1,sK4,X0_55) = k7_relat_1(sK4,u1_struct_0(X0_55))
% 2.36/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_2779,c_2673]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2790,plain,
% 2.36/1.00      ( k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1055,c_2784]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_10,plain,
% 2.36/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.36/1.00      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 2.36/1.00      | ~ l1_struct_0(X3)
% 2.36/1.00      | ~ l1_struct_0(X2)
% 2.36/1.00      | ~ l1_struct_0(X1)
% 2.36/1.00      | ~ v1_funct_1(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_534,plain,
% 2.36/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.36/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.36/1.00      | m1_subset_1(k2_tmap_1(X0_55,X1_55,X0_53,X2_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 2.36/1.00      | ~ l1_struct_0(X2_55)
% 2.36/1.00      | ~ l1_struct_0(X1_55)
% 2.36/1.00      | ~ l1_struct_0(X0_55)
% 2.36/1.00      | ~ v1_funct_1(X0_53) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1051,plain,
% 2.36/1.00      ( v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 2.36/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.36/1.00      | m1_subset_1(k2_tmap_1(X0_55,X1_55,X0_53,X2_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
% 2.36/1.00      | l1_struct_0(X2_55) != iProver_top
% 2.36/1.00      | l1_struct_0(X1_55) != iProver_top
% 2.36/1.00      | l1_struct_0(X0_55) != iProver_top
% 2.36/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2827,plain,
% 2.36/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.36/1.00      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 2.36/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.36/1.00      | l1_struct_0(sK2) != iProver_top
% 2.36/1.00      | l1_struct_0(sK1) != iProver_top
% 2.36/1.00      | l1_struct_0(sK3) != iProver_top
% 2.36/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_2790,c_1051]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_42,plain,
% 2.36/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_6,plain,
% 2.36/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_62,plain,
% 2.36/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_64,plain,
% 2.36/1.00      ( l1_struct_0(sK1) = iProver_top
% 2.36/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_62]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_538,plain,
% 2.36/1.00      ( l1_struct_0(X0_55) | ~ l1_pre_topc(X0_55) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1418,plain,
% 2.36/1.00      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_538]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1419,plain,
% 2.36/1.00      ( l1_struct_0(sK3) = iProver_top
% 2.36/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1418]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1048,plain,
% 2.36/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.36/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | l1_pre_topc(X0_55) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1751,plain,
% 2.36/1.00      ( l1_pre_topc(sK2) = iProver_top
% 2.36/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1055,c_1048]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1952,plain,
% 2.36/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_1751,c_32,c_39,c_1547]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1047,plain,
% 2.36/1.00      ( l1_struct_0(X0_55) = iProver_top
% 2.36/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1957,plain,
% 2.36/1.00      ( l1_struct_0(sK2) = iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1952,c_1047]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3302,plain,
% 2.36/1.00      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_2827,c_32,c_35,c_39,c_40,c_41,c_42,c_64,c_1419,c_1547,
% 2.36/1.00                 c_1957]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.36/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_541,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.36/1.00      | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1044,plain,
% 2.36/1.00      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 2.36/1.00      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3312,plain,
% 2.36/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),X0_53) = k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),X0_53) ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_3302,c_1044]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_22,negated_conjecture,
% 2.36/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_523,negated_conjecture,
% 2.36/1.00      ( m1_pre_topc(sK2,sK0) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1061,plain,
% 2.36/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_9,plain,
% 2.36/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.36/1.00      | ~ m1_pre_topc(X3,X4)
% 2.36/1.00      | ~ m1_pre_topc(X3,X1)
% 2.36/1.00      | ~ m1_pre_topc(X1,X4)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.36/1.00      | v2_struct_0(X4)
% 2.36/1.00      | v2_struct_0(X2)
% 2.36/1.00      | ~ l1_pre_topc(X4)
% 2.36/1.00      | ~ l1_pre_topc(X2)
% 2.36/1.00      | ~ v2_pre_topc(X4)
% 2.36/1.00      | ~ v2_pre_topc(X2)
% 2.36/1.00      | ~ v1_funct_1(X0)
% 2.36/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_535,plain,
% 2.36/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.36/1.00      | ~ m1_pre_topc(X2_55,X3_55)
% 2.36/1.00      | ~ m1_pre_topc(X2_55,X0_55)
% 2.36/1.00      | ~ m1_pre_topc(X0_55,X3_55)
% 2.36/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.36/1.00      | v2_struct_0(X3_55)
% 2.36/1.00      | v2_struct_0(X1_55)
% 2.36/1.00      | ~ l1_pre_topc(X3_55)
% 2.36/1.00      | ~ l1_pre_topc(X1_55)
% 2.36/1.00      | ~ v2_pre_topc(X3_55)
% 2.36/1.00      | ~ v2_pre_topc(X1_55)
% 2.36/1.00      | ~ v1_funct_1(X0_53)
% 2.36/1.00      | k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1050,plain,
% 2.36/1.00      ( k2_partfun1(u1_struct_0(X0_55),u1_struct_0(X1_55),X0_53,u1_struct_0(X2_55)) = k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_53)
% 2.36/1.00      | v1_funct_2(X0_53,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 2.36/1.00      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 2.36/1.00      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 2.36/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 2.36/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.36/1.00      | v2_struct_0(X3_55) = iProver_top
% 2.36/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | l1_pre_topc(X3_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(X3_55) != iProver_top
% 2.36/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2494,plain,
% 2.36/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 2.36/1.00      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.36/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 2.36/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.36/1.00      | v2_struct_0(sK1) = iProver_top
% 2.36/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.36/1.00      | v2_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.36/1.00      | v1_funct_1(sK4) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1056,c_1050]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2866,plain,
% 2.36/1.00      ( l1_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 2.36/1.00      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.36/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 2.36/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.36/1.00      | v2_pre_topc(X1_55) != iProver_top ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_2494,c_33,c_34,c_35,c_40,c_41]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2867,plain,
% 2.36/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_55)) = k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4)
% 2.36/1.00      | m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.36/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 2.36/1.00      | v2_struct_0(X1_55) = iProver_top
% 2.36/1.00      | l1_pre_topc(X1_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(X1_55) != iProver_top ),
% 2.36/1.00      inference(renaming,[status(thm)],[c_2866]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2872,plain,
% 2.36/1.00      ( k3_tmap_1(X0_55,sK1,sK3,X1_55,sK4) = k7_relat_1(sK4,u1_struct_0(X1_55))
% 2.36/1.00      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 2.36/1.00      | m1_pre_topc(X1_55,sK3) != iProver_top
% 2.36/1.00      | m1_pre_topc(sK3,X0_55) != iProver_top
% 2.36/1.00      | v2_struct_0(X0_55) = iProver_top
% 2.36/1.00      | l1_pre_topc(X0_55) != iProver_top
% 2.36/1.00      | v2_pre_topc(X0_55) != iProver_top ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_2867,c_2673]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2883,plain,
% 2.36/1.00      ( k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55))
% 2.36/1.00      | m1_pre_topc(X0_55,sK0) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 2.36/1.00      | v2_struct_0(sK0) = iProver_top
% 2.36/1.00      | l1_pre_topc(sK0) != iProver_top
% 2.36/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1059,c_2872]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_29,negated_conjecture,
% 2.36/1.00      ( ~ v2_struct_0(sK0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_30,plain,
% 2.36/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2948,plain,
% 2.36/1.00      ( m1_pre_topc(X0_55,sK3) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,sK0) != iProver_top
% 2.36/1.00      | k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55)) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_2883,c_30,c_31,c_32]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2949,plain,
% 2.36/1.00      ( k3_tmap_1(sK0,sK1,sK3,X0_55,sK4) = k7_relat_1(sK4,u1_struct_0(X0_55))
% 2.36/1.00      | m1_pre_topc(X0_55,sK0) != iProver_top
% 2.36/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 2.36/1.00      inference(renaming,[status(thm)],[c_2948]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2958,plain,
% 2.36/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 2.36/1.00      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1061,c_2949]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_43,plain,
% 2.36/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3087,plain,
% 2.36/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_2958,c_43]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1681,plain,
% 2.36/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k10_relat_1(sK4,X0_53) ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1056,c_1044]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_13,negated_conjecture,
% 2.36/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 2.36/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_531,negated_conjecture,
% 2.36/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2036,plain,
% 2.36/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k10_relat_1(sK4,sK5) ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_1681,c_531]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3090,plain,
% 2.36/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k10_relat_1(sK4,sK5) ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_3087,c_2036]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3479,plain,
% 2.36/1.00      ( k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k10_relat_1(sK4,sK5) ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_3312,c_3090]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_4,plain,
% 2.36/1.00      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 2.36/1.00      | ~ v1_funct_1(X0)
% 2.36/1.00      | ~ v1_relat_1(X0)
% 2.36/1.00      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_14,negated_conjecture,
% 2.36/1.00      ( r1_tarski(k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5),u1_struct_0(sK2)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_303,plain,
% 2.36/1.00      ( ~ v1_funct_1(X0)
% 2.36/1.00      | ~ v1_relat_1(X0)
% 2.36/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k10_relat_1(X0,X1)
% 2.36/1.00      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
% 2.36/1.00      | u1_struct_0(sK2) != X2 ),
% 2.36/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_304,plain,
% 2.36/1.00      ( ~ v1_funct_1(X0)
% 2.36/1.00      | ~ v1_relat_1(X0)
% 2.36/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k10_relat_1(X0,X1)
% 2.36/1.00      | k10_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),X1) = k10_relat_1(X0,X1) ),
% 2.36/1.00      inference(unflattening,[status(thm)],[c_303]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_515,plain,
% 2.36/1.00      ( ~ v1_funct_1(X0_53)
% 2.36/1.00      | ~ v1_relat_1(X0_53)
% 2.36/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k10_relat_1(X0_53,X1_53)
% 2.36/1.00      | k10_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),X1_53) = k10_relat_1(X0_53,X1_53) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_304]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1525,plain,
% 2.36/1.00      ( ~ v1_funct_1(sK4)
% 2.36/1.00      | ~ v1_relat_1(sK4)
% 2.36/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k10_relat_1(sK4,sK5)
% 2.36/1.00      | k10_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k10_relat_1(sK4,sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_515]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1,plain,
% 2.36/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_542,plain,
% 2.36/1.00      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1490,plain,
% 2.36/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_542]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_0,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.00      | ~ v1_relat_1(X1)
% 2.36/1.00      | v1_relat_1(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_543,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.36/1.00      | ~ v1_relat_1(X1_53)
% 2.36/1.00      | v1_relat_1(X0_53) ),
% 2.36/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1308,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 2.36/1.00      | v1_relat_1(X0_53)
% 2.36/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_543]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1423,plain,
% 2.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.36/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
% 2.36/1.00      | v1_relat_1(sK4) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1308]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1334,plain,
% 2.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.36/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k10_relat_1(sK4,X0_53) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_541]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1408,plain,
% 2.36/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.36/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k10_relat_1(sK4,sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1334]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(contradiction,plain,
% 2.36/1.00      ( $false ),
% 2.36/1.00      inference(minisat,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_3479,c_1525,c_1490,c_1423,c_1408,c_17,c_19]) ).
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  ------                               Statistics
% 2.36/1.00  
% 2.36/1.00  ------ General
% 2.36/1.00  
% 2.36/1.00  abstr_ref_over_cycles:                  0
% 2.36/1.00  abstr_ref_under_cycles:                 0
% 2.36/1.00  gc_basic_clause_elim:                   0
% 2.36/1.00  forced_gc_time:                         0
% 2.36/1.00  parsing_time:                           0.009
% 2.36/1.00  unif_index_cands_time:                  0.
% 2.36/1.00  unif_index_add_time:                    0.
% 2.36/1.00  orderings_time:                         0.
% 2.36/1.00  out_proof_time:                         0.011
% 2.36/1.00  total_time:                             0.162
% 2.36/1.00  num_of_symbols:                         60
% 2.36/1.00  num_of_terms:                           3343
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing
% 2.36/1.00  
% 2.36/1.00  num_of_splits:                          0
% 2.36/1.00  num_of_split_atoms:                     0
% 2.36/1.00  num_of_reused_defs:                     0
% 2.36/1.00  num_eq_ax_congr_red:                    35
% 2.36/1.00  num_of_sem_filtered_clauses:            1
% 2.36/1.00  num_of_subtypes:                        4
% 2.36/1.00  monotx_restored_types:                  0
% 2.36/1.00  sat_num_of_epr_types:                   0
% 2.36/1.00  sat_num_of_non_cyclic_types:            0
% 2.36/1.00  sat_guarded_non_collapsed_types:        0
% 2.36/1.00  num_pure_diseq_elim:                    0
% 2.36/1.00  simp_replaced_by:                       0
% 2.36/1.00  res_preprocessed:                       150
% 2.36/1.00  prep_upred:                             0
% 2.36/1.00  prep_unflattend:                        1
% 2.36/1.00  smt_new_axioms:                         0
% 2.36/1.00  pred_elim_cands:                        9
% 2.36/1.00  pred_elim:                              1
% 2.36/1.00  pred_elim_cl:                           1
% 2.36/1.00  pred_elim_cycles:                       3
% 2.36/1.00  merged_defs:                            0
% 2.36/1.00  merged_defs_ncl:                        0
% 2.36/1.00  bin_hyper_res:                          0
% 2.36/1.00  prep_cycles:                            4
% 2.36/1.00  pred_elim_time:                         0.011
% 2.36/1.00  splitting_time:                         0.
% 2.36/1.00  sem_filter_time:                        0.
% 2.36/1.00  monotx_time:                            0.
% 2.36/1.00  subtype_inf_time:                       0.
% 2.36/1.00  
% 2.36/1.00  ------ Problem properties
% 2.36/1.00  
% 2.36/1.00  clauses:                                29
% 2.36/1.00  conjectures:                            16
% 2.36/1.00  epr:                                    15
% 2.36/1.00  horn:                                   27
% 2.36/1.00  ground:                                 16
% 2.36/1.00  unary:                                  17
% 2.36/1.00  binary:                                 2
% 2.36/1.00  lits:                                   83
% 2.36/1.00  lits_eq:                                7
% 2.36/1.00  fd_pure:                                0
% 2.36/1.00  fd_pseudo:                              0
% 2.36/1.00  fd_cond:                                0
% 2.36/1.00  fd_pseudo_cond:                         0
% 2.36/1.00  ac_symbols:                             0
% 2.36/1.00  
% 2.36/1.00  ------ Propositional Solver
% 2.36/1.00  
% 2.36/1.00  prop_solver_calls:                      29
% 2.36/1.00  prop_fast_solver_calls:                 1057
% 2.36/1.00  smt_solver_calls:                       0
% 2.36/1.00  smt_fast_solver_calls:                  0
% 2.36/1.00  prop_num_of_clauses:                    1089
% 2.36/1.00  prop_preprocess_simplified:             4395
% 2.36/1.00  prop_fo_subsumed:                       45
% 2.36/1.00  prop_solver_time:                       0.
% 2.36/1.00  smt_solver_time:                        0.
% 2.36/1.00  smt_fast_solver_time:                   0.
% 2.36/1.00  prop_fast_solver_time:                  0.
% 2.36/1.00  prop_unsat_core_time:                   0.
% 2.36/1.00  
% 2.36/1.00  ------ QBF
% 2.36/1.00  
% 2.36/1.00  qbf_q_res:                              0
% 2.36/1.00  qbf_num_tautologies:                    0
% 2.36/1.00  qbf_prep_cycles:                        0
% 2.36/1.00  
% 2.36/1.00  ------ BMC1
% 2.36/1.00  
% 2.36/1.00  bmc1_current_bound:                     -1
% 2.36/1.00  bmc1_last_solved_bound:                 -1
% 2.36/1.00  bmc1_unsat_core_size:                   -1
% 2.36/1.00  bmc1_unsat_core_parents_size:           -1
% 2.36/1.00  bmc1_merge_next_fun:                    0
% 2.36/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.36/1.00  
% 2.36/1.00  ------ Instantiation
% 2.36/1.00  
% 2.36/1.00  inst_num_of_clauses:                    371
% 2.36/1.00  inst_num_in_passive:                    10
% 2.36/1.00  inst_num_in_active:                     255
% 2.36/1.00  inst_num_in_unprocessed:                106
% 2.36/1.00  inst_num_of_loops:                      280
% 2.36/1.00  inst_num_of_learning_restarts:          0
% 2.36/1.00  inst_num_moves_active_passive:          20
% 2.36/1.00  inst_lit_activity:                      0
% 2.36/1.00  inst_lit_activity_moves:                0
% 2.36/1.00  inst_num_tautologies:                   0
% 2.36/1.00  inst_num_prop_implied:                  0
% 2.36/1.00  inst_num_existing_simplified:           0
% 2.36/1.00  inst_num_eq_res_simplified:             0
% 2.36/1.00  inst_num_child_elim:                    0
% 2.36/1.00  inst_num_of_dismatching_blockings:      65
% 2.36/1.00  inst_num_of_non_proper_insts:           344
% 2.36/1.00  inst_num_of_duplicates:                 0
% 2.36/1.00  inst_inst_num_from_inst_to_res:         0
% 2.36/1.00  inst_dismatching_checking_time:         0.
% 2.36/1.00  
% 2.36/1.00  ------ Resolution
% 2.36/1.00  
% 2.36/1.00  res_num_of_clauses:                     0
% 2.36/1.00  res_num_in_passive:                     0
% 2.36/1.00  res_num_in_active:                      0
% 2.36/1.00  res_num_of_loops:                       154
% 2.36/1.00  res_forward_subset_subsumed:            76
% 2.36/1.00  res_backward_subset_subsumed:           0
% 2.36/1.00  res_forward_subsumed:                   0
% 2.36/1.00  res_backward_subsumed:                  0
% 2.36/1.00  res_forward_subsumption_resolution:     0
% 2.36/1.00  res_backward_subsumption_resolution:    0
% 2.36/1.00  res_clause_to_clause_subsumption:       98
% 2.36/1.00  res_orphan_elimination:                 0
% 2.36/1.00  res_tautology_del:                      67
% 2.36/1.00  res_num_eq_res_simplified:              0
% 2.36/1.00  res_num_sel_changes:                    0
% 2.36/1.00  res_moves_from_active_to_pass:          0
% 2.36/1.00  
% 2.36/1.00  ------ Superposition
% 2.36/1.00  
% 2.36/1.00  sup_time_total:                         0.
% 2.36/1.00  sup_time_generating:                    0.
% 2.36/1.00  sup_time_sim_full:                      0.
% 2.36/1.00  sup_time_sim_immed:                     0.
% 2.36/1.00  
% 2.36/1.00  sup_num_of_clauses:                     64
% 2.36/1.00  sup_num_in_active:                      51
% 2.36/1.00  sup_num_in_passive:                     13
% 2.36/1.00  sup_num_of_loops:                       55
% 2.36/1.00  sup_fw_superposition:                   18
% 2.36/1.00  sup_bw_superposition:                   18
% 2.36/1.00  sup_immediate_simplified:               0
% 2.36/1.00  sup_given_eliminated:                   0
% 2.36/1.00  comparisons_done:                       0
% 2.36/1.00  comparisons_avoided:                    0
% 2.36/1.00  
% 2.36/1.00  ------ Simplifications
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  sim_fw_subset_subsumed:                 0
% 2.36/1.00  sim_bw_subset_subsumed:                 0
% 2.36/1.00  sim_fw_subsumed:                        0
% 2.36/1.00  sim_bw_subsumed:                        0
% 2.36/1.00  sim_fw_subsumption_res:                 1
% 2.36/1.00  sim_bw_subsumption_res:                 0
% 2.36/1.00  sim_tautology_del:                      0
% 2.36/1.00  sim_eq_tautology_del:                   0
% 2.36/1.00  sim_eq_res_simp:                        0
% 2.36/1.00  sim_fw_demodulated:                     2
% 2.36/1.00  sim_bw_demodulated:                     4
% 2.36/1.00  sim_light_normalised:                   0
% 2.36/1.00  sim_joinable_taut:                      0
% 2.36/1.00  sim_joinable_simp:                      0
% 2.36/1.00  sim_ac_normalised:                      0
% 2.36/1.00  sim_smt_subsumption:                    0
% 2.36/1.00  
%------------------------------------------------------------------------------
