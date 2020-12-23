%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:55 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 756 expanded)
%              Number of clauses        :  106 ( 187 expanded)
%              Number of leaves         :   17 ( 313 expanded)
%              Depth                    :   21
%              Number of atoms          :  720 (9443 expanded)
%              Number of equality atoms :  213 ( 968 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)
          & r1_tarski(X5,u1_struct_0(X2))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5)
        & r1_tarski(sK5,u1_struct_0(X2))
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f29,f35,f34,f33,f32,f31,f30])).

fof(f62,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_514,negated_conjecture,
    ( m1_pre_topc(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_983,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_513,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_984,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f44])).

cnf(c_521,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X0_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X0_57)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_53,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_53,X2_57) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_977,plain,
    ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_53,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_53,X2_57)
    | v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_2200,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k2_tmap_1(sK3,sK1,sK4,X0_57)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_57,sK3) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_977])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_30,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_31,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_32,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_33,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_38,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_40,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_522,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ l1_pre_topc(X1_57)
    | l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1336,plain,
    ( ~ m1_pre_topc(sK3,X0_57)
    | ~ l1_pre_topc(X0_57)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_1378,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_1379,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1378])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_524,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ l1_pre_topc(X1_57)
    | ~ v2_pre_topc(X1_57)
    | v2_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1432,plain,
    ( ~ m1_pre_topc(sK3,X0_57)
    | ~ l1_pre_topc(X0_57)
    | ~ v2_pre_topc(X0_57)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_1578,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_1579,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1578])).

cnf(c_2703,plain,
    ( m1_pre_topc(X0_57,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k2_tmap_1(sK3,sK1,sK4,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_30,c_31,c_32,c_33,c_34,c_37,c_38,c_39,c_40,c_1379,c_1579])).

cnf(c_2704,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k2_tmap_1(sK3,sK1,sK4,X0_57)
    | m1_pre_topc(X0_57,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2703])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X0_55,X1_55,X0_53,X2_55) = k7_relat_1(X0_53,X2_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_973,plain,
    ( k2_partfun1(X0_55,X1_55,X0_53,X2_55) = k7_relat_1(X0_53,X2_55)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1597,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_973])).

cnf(c_1235,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_2630,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1597,c_18,c_16,c_1235])).

cnf(c_2709,plain,
    ( k2_tmap_1(sK3,sK1,sK4,X0_57) = k7_relat_1(sK4,u1_struct_0(X0_57))
    | m1_pre_topc(X0_57,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2704,c_2630])).

cnf(c_2715,plain,
    ( k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_983,c_2709])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_519,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | m1_subset_1(k2_tmap_1(X0_57,X1_57,X0_53,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
    | ~ l1_struct_0(X2_57)
    | ~ l1_struct_0(X1_57)
    | ~ l1_struct_0(X0_57)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_979,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_57,X1_57,X0_53,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) = iProver_top
    | l1_struct_0(X2_57) != iProver_top
    | l1_struct_0(X1_57) != iProver_top
    | l1_struct_0(X0_57) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_2841,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_979])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_61,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_63,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_523,plain,
    ( l1_struct_0(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1331,plain,
    ( l1_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_1332,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1331])).

cnf(c_976,plain,
    ( m1_pre_topc(X0_57,X1_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_1682,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_983,c_976])).

cnf(c_1986,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1682,c_31,c_38,c_1379])).

cnf(c_975,plain,
    ( l1_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1991,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_975])).

cnf(c_3246,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2841,c_31,c_34,c_38,c_39,c_40,c_41,c_63,c_1332,c_1379,c_1991])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k7_relset_1(X0_55,X1_55,X0_53,X1_53) = k9_relat_1(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_972,plain,
    ( k7_relset_1(X0_55,X1_55,X0_53,X1_53) = k9_relat_1(X0_53,X1_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_3253,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),X0_53) = k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),X0_53) ),
    inference(superposition,[status(thm)],[c_3246,c_972])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_508,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_989,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_510,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_987,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f45])).

cnf(c_520,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | v2_struct_0(X3_57)
    | v2_struct_0(X1_57)
    | ~ l1_pre_topc(X3_57)
    | ~ l1_pre_topc(X1_57)
    | ~ v2_pre_topc(X3_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_53,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_978,plain,
    ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_53,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_53)
    | v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_2436,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK1,sK3,X0_57,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_984,c_978])).

cnf(c_2880,plain,
    ( l1_pre_topc(X1_57) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK1,sK3,X0_57,sK4)
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2436,c_32,c_33,c_34,c_39,c_40])).

cnf(c_2881,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK1,sK3,X0_57,sK4)
    | m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X0_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_2880])).

cnf(c_2886,plain,
    ( k3_tmap_1(X0_57,sK1,sK3,X1_57,sK4) = k7_relat_1(sK4,u1_struct_0(X1_57))
    | m1_pre_topc(X1_57,X0_57) != iProver_top
    | m1_pre_topc(X1_57,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2881,c_2630])).

cnf(c_2897,plain,
    ( k3_tmap_1(sK0,sK1,sK3,X0_57,sK4) = k7_relat_1(sK4,u1_struct_0(X0_57))
    | m1_pre_topc(X0_57,sK0) != iProver_top
    | m1_pre_topc(X0_57,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_2886])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_29,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3046,plain,
    ( m1_pre_topc(X0_57,sK3) != iProver_top
    | m1_pre_topc(X0_57,sK0) != iProver_top
    | k3_tmap_1(sK0,sK1,sK3,X0_57,sK4) = k7_relat_1(sK4,u1_struct_0(X0_57)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2897,c_29,c_30,c_31])).

cnf(c_3047,plain,
    ( k3_tmap_1(sK0,sK1,sK3,X0_57,sK4) = k7_relat_1(sK4,u1_struct_0(X0_57))
    | m1_pre_topc(X0_57,sK0) != iProver_top
    | m1_pre_topc(X0_57,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3046])).

cnf(c_3056,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_3047])).

cnf(c_42,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3119,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3056,c_42])).

cnf(c_1525,plain,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k9_relat_1(sK4,X0_53) ),
    inference(superposition,[status(thm)],[c_984,c_972])).

cnf(c_12,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_516,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1528,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_1525,c_516])).

cnf(c_3122,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3119,c_1528])).

cnf(c_3336,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_3253,c_3122])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_294,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | u1_struct_0(sK2) != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_295,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
    inference(resolution,[status(thm)],[c_1,c_295])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k9_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_53,sK5) ),
    inference(subtyping,[status(esa)],[c_309])).

cnf(c_997,plain,
    ( k9_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_53,sK5)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_1577,plain,
    ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_984,c_997])).

cnf(c_3337,plain,
    ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3336,c_1577])).

cnf(c_3338,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3337])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:49:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.32/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/0.98  
% 2.32/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/0.98  
% 2.32/0.98  ------  iProver source info
% 2.32/0.98  
% 2.32/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.32/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/0.98  git: non_committed_changes: false
% 2.32/0.98  git: last_make_outside_of_git: false
% 2.32/0.98  
% 2.32/0.98  ------ 
% 2.32/0.98  
% 2.32/0.98  ------ Input Options
% 2.32/0.98  
% 2.32/0.98  --out_options                           all
% 2.32/0.98  --tptp_safe_out                         true
% 2.32/0.98  --problem_path                          ""
% 2.32/0.98  --include_path                          ""
% 2.32/0.98  --clausifier                            res/vclausify_rel
% 2.32/0.98  --clausifier_options                    --mode clausify
% 2.32/0.98  --stdin                                 false
% 2.32/0.98  --stats_out                             all
% 2.32/0.98  
% 2.32/0.98  ------ General Options
% 2.32/0.98  
% 2.32/0.98  --fof                                   false
% 2.32/0.98  --time_out_real                         305.
% 2.32/0.98  --time_out_virtual                      -1.
% 2.32/0.98  --symbol_type_check                     false
% 2.32/0.98  --clausify_out                          false
% 2.32/0.98  --sig_cnt_out                           false
% 2.32/0.98  --trig_cnt_out                          false
% 2.32/0.98  --trig_cnt_out_tolerance                1.
% 2.32/0.98  --trig_cnt_out_sk_spl                   false
% 2.32/0.98  --abstr_cl_out                          false
% 2.32/0.98  
% 2.32/0.98  ------ Global Options
% 2.32/0.98  
% 2.32/0.98  --schedule                              default
% 2.32/0.98  --add_important_lit                     false
% 2.32/0.98  --prop_solver_per_cl                    1000
% 2.32/0.98  --min_unsat_core                        false
% 2.32/0.98  --soft_assumptions                      false
% 2.32/0.98  --soft_lemma_size                       3
% 2.32/0.98  --prop_impl_unit_size                   0
% 2.32/0.98  --prop_impl_unit                        []
% 2.32/0.98  --share_sel_clauses                     true
% 2.32/0.98  --reset_solvers                         false
% 2.32/0.98  --bc_imp_inh                            [conj_cone]
% 2.32/0.98  --conj_cone_tolerance                   3.
% 2.32/0.98  --extra_neg_conj                        none
% 2.32/0.98  --large_theory_mode                     true
% 2.32/0.98  --prolific_symb_bound                   200
% 2.32/0.98  --lt_threshold                          2000
% 2.32/0.98  --clause_weak_htbl                      true
% 2.32/0.98  --gc_record_bc_elim                     false
% 2.32/0.98  
% 2.32/0.98  ------ Preprocessing Options
% 2.32/0.98  
% 2.32/0.98  --preprocessing_flag                    true
% 2.32/0.98  --time_out_prep_mult                    0.1
% 2.32/0.98  --splitting_mode                        input
% 2.32/0.98  --splitting_grd                         true
% 2.32/0.98  --splitting_cvd                         false
% 2.32/0.98  --splitting_cvd_svl                     false
% 2.32/0.98  --splitting_nvd                         32
% 2.32/0.98  --sub_typing                            true
% 2.32/0.98  --prep_gs_sim                           true
% 2.32/0.98  --prep_unflatten                        true
% 2.32/0.98  --prep_res_sim                          true
% 2.32/0.98  --prep_upred                            true
% 2.32/0.98  --prep_sem_filter                       exhaustive
% 2.32/0.98  --prep_sem_filter_out                   false
% 2.32/0.98  --pred_elim                             true
% 2.32/0.98  --res_sim_input                         true
% 2.32/0.98  --eq_ax_congr_red                       true
% 2.32/0.98  --pure_diseq_elim                       true
% 2.32/0.98  --brand_transform                       false
% 2.32/0.98  --non_eq_to_eq                          false
% 2.32/0.98  --prep_def_merge                        true
% 2.32/0.98  --prep_def_merge_prop_impl              false
% 2.32/0.98  --prep_def_merge_mbd                    true
% 2.32/0.98  --prep_def_merge_tr_red                 false
% 2.32/0.98  --prep_def_merge_tr_cl                  false
% 2.32/0.98  --smt_preprocessing                     true
% 2.32/0.98  --smt_ac_axioms                         fast
% 2.32/0.98  --preprocessed_out                      false
% 2.32/0.98  --preprocessed_stats                    false
% 2.32/0.98  
% 2.32/0.98  ------ Abstraction refinement Options
% 2.32/0.98  
% 2.32/0.98  --abstr_ref                             []
% 2.32/0.98  --abstr_ref_prep                        false
% 2.32/0.98  --abstr_ref_until_sat                   false
% 2.32/0.98  --abstr_ref_sig_restrict                funpre
% 2.32/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.98  --abstr_ref_under                       []
% 2.32/0.98  
% 2.32/0.98  ------ SAT Options
% 2.32/0.98  
% 2.32/0.98  --sat_mode                              false
% 2.32/0.98  --sat_fm_restart_options                ""
% 2.32/0.98  --sat_gr_def                            false
% 2.32/0.98  --sat_epr_types                         true
% 2.32/0.98  --sat_non_cyclic_types                  false
% 2.32/0.98  --sat_finite_models                     false
% 2.32/0.98  --sat_fm_lemmas                         false
% 2.32/0.98  --sat_fm_prep                           false
% 2.32/0.98  --sat_fm_uc_incr                        true
% 2.32/0.98  --sat_out_model                         small
% 2.32/0.98  --sat_out_clauses                       false
% 2.32/0.98  
% 2.32/0.98  ------ QBF Options
% 2.32/0.98  
% 2.32/0.98  --qbf_mode                              false
% 2.32/0.98  --qbf_elim_univ                         false
% 2.32/0.98  --qbf_dom_inst                          none
% 2.32/0.98  --qbf_dom_pre_inst                      false
% 2.32/0.98  --qbf_sk_in                             false
% 2.32/0.98  --qbf_pred_elim                         true
% 2.32/0.98  --qbf_split                             512
% 2.32/0.98  
% 2.32/0.98  ------ BMC1 Options
% 2.32/0.98  
% 2.32/0.98  --bmc1_incremental                      false
% 2.32/0.98  --bmc1_axioms                           reachable_all
% 2.32/0.98  --bmc1_min_bound                        0
% 2.32/0.98  --bmc1_max_bound                        -1
% 2.32/0.98  --bmc1_max_bound_default                -1
% 2.32/0.98  --bmc1_symbol_reachability              true
% 2.32/0.98  --bmc1_property_lemmas                  false
% 2.32/0.98  --bmc1_k_induction                      false
% 2.32/0.98  --bmc1_non_equiv_states                 false
% 2.32/0.98  --bmc1_deadlock                         false
% 2.32/0.98  --bmc1_ucm                              false
% 2.32/0.98  --bmc1_add_unsat_core                   none
% 2.32/0.98  --bmc1_unsat_core_children              false
% 2.32/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.98  --bmc1_out_stat                         full
% 2.32/0.98  --bmc1_ground_init                      false
% 2.32/0.98  --bmc1_pre_inst_next_state              false
% 2.32/0.98  --bmc1_pre_inst_state                   false
% 2.32/0.98  --bmc1_pre_inst_reach_state             false
% 2.32/0.98  --bmc1_out_unsat_core                   false
% 2.32/0.98  --bmc1_aig_witness_out                  false
% 2.32/0.98  --bmc1_verbose                          false
% 2.32/0.98  --bmc1_dump_clauses_tptp                false
% 2.32/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.98  --bmc1_dump_file                        -
% 2.32/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.98  --bmc1_ucm_extend_mode                  1
% 2.32/0.98  --bmc1_ucm_init_mode                    2
% 2.32/0.98  --bmc1_ucm_cone_mode                    none
% 2.32/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.98  --bmc1_ucm_relax_model                  4
% 2.32/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.98  --bmc1_ucm_layered_model                none
% 2.32/0.98  --bmc1_ucm_max_lemma_size               10
% 2.32/0.98  
% 2.32/0.98  ------ AIG Options
% 2.32/0.98  
% 2.32/0.98  --aig_mode                              false
% 2.32/0.98  
% 2.32/0.98  ------ Instantiation Options
% 2.32/0.98  
% 2.32/0.98  --instantiation_flag                    true
% 2.32/0.98  --inst_sos_flag                         false
% 2.32/0.98  --inst_sos_phase                        true
% 2.32/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.98  --inst_lit_sel_side                     num_symb
% 2.32/0.98  --inst_solver_per_active                1400
% 2.32/0.98  --inst_solver_calls_frac                1.
% 2.32/0.98  --inst_passive_queue_type               priority_queues
% 2.32/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.98  --inst_passive_queues_freq              [25;2]
% 2.32/0.98  --inst_dismatching                      true
% 2.32/0.98  --inst_eager_unprocessed_to_passive     true
% 2.32/0.98  --inst_prop_sim_given                   true
% 2.32/0.98  --inst_prop_sim_new                     false
% 2.32/0.98  --inst_subs_new                         false
% 2.32/0.98  --inst_eq_res_simp                      false
% 2.32/0.98  --inst_subs_given                       false
% 2.32/0.98  --inst_orphan_elimination               true
% 2.32/0.98  --inst_learning_loop_flag               true
% 2.32/0.98  --inst_learning_start                   3000
% 2.32/0.98  --inst_learning_factor                  2
% 2.32/0.98  --inst_start_prop_sim_after_learn       3
% 2.32/0.98  --inst_sel_renew                        solver
% 2.32/0.98  --inst_lit_activity_flag                true
% 2.32/0.98  --inst_restr_to_given                   false
% 2.32/0.98  --inst_activity_threshold               500
% 2.32/0.98  --inst_out_proof                        true
% 2.32/0.98  
% 2.32/0.98  ------ Resolution Options
% 2.32/0.98  
% 2.32/0.98  --resolution_flag                       true
% 2.32/0.98  --res_lit_sel                           adaptive
% 2.32/0.98  --res_lit_sel_side                      none
% 2.32/0.98  --res_ordering                          kbo
% 2.32/0.98  --res_to_prop_solver                    active
% 2.32/0.98  --res_prop_simpl_new                    false
% 2.32/0.98  --res_prop_simpl_given                  true
% 2.32/0.98  --res_passive_queue_type                priority_queues
% 2.32/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.98  --res_passive_queues_freq               [15;5]
% 2.32/0.98  --res_forward_subs                      full
% 2.32/0.98  --res_backward_subs                     full
% 2.32/0.98  --res_forward_subs_resolution           true
% 2.32/0.98  --res_backward_subs_resolution          true
% 2.32/0.98  --res_orphan_elimination                true
% 2.32/0.98  --res_time_limit                        2.
% 2.32/0.98  --res_out_proof                         true
% 2.32/0.98  
% 2.32/0.98  ------ Superposition Options
% 2.32/0.98  
% 2.32/0.98  --superposition_flag                    true
% 2.32/0.98  --sup_passive_queue_type                priority_queues
% 2.32/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.98  --demod_completeness_check              fast
% 2.32/0.98  --demod_use_ground                      true
% 2.32/0.98  --sup_to_prop_solver                    passive
% 2.32/0.98  --sup_prop_simpl_new                    true
% 2.32/0.98  --sup_prop_simpl_given                  true
% 2.32/0.98  --sup_fun_splitting                     false
% 2.32/0.98  --sup_smt_interval                      50000
% 2.32/0.98  
% 2.32/0.98  ------ Superposition Simplification Setup
% 2.32/0.98  
% 2.32/0.98  --sup_indices_passive                   []
% 2.32/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.98  --sup_full_bw                           [BwDemod]
% 2.32/0.98  --sup_immed_triv                        [TrivRules]
% 2.32/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.98  --sup_immed_bw_main                     []
% 2.32/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.98  
% 2.32/0.98  ------ Combination Options
% 2.32/0.98  
% 2.32/0.98  --comb_res_mult                         3
% 2.32/0.98  --comb_sup_mult                         2
% 2.32/0.98  --comb_inst_mult                        10
% 2.32/0.98  
% 2.32/0.98  ------ Debug Options
% 2.32/0.98  
% 2.32/0.98  --dbg_backtrace                         false
% 2.32/0.98  --dbg_dump_prop_clauses                 false
% 2.32/0.98  --dbg_dump_prop_clauses_file            -
% 2.32/0.98  --dbg_out_stat                          false
% 2.32/0.98  ------ Parsing...
% 2.32/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/0.98  
% 2.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.32/0.98  
% 2.32/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/0.98  
% 2.32/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/0.98  ------ Proving...
% 2.32/0.98  ------ Problem Properties 
% 2.32/0.98  
% 2.32/0.98  
% 2.32/0.98  clauses                                 27
% 2.32/0.98  conjectures                             16
% 2.32/0.98  EPR                                     15
% 2.32/0.98  Horn                                    25
% 2.32/0.98  unary                                   16
% 2.32/0.98  binary                                  3
% 2.32/0.98  lits                                    77
% 2.32/0.98  lits eq                                 6
% 2.32/0.98  fd_pure                                 0
% 2.32/0.98  fd_pseudo                               0
% 2.32/0.98  fd_cond                                 0
% 2.32/0.98  fd_pseudo_cond                          0
% 2.32/0.98  AC symbols                              0
% 2.32/0.98  
% 2.32/0.98  ------ Schedule dynamic 5 is on 
% 2.32/0.98  
% 2.32/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/0.98  
% 2.32/0.98  
% 2.32/0.98  ------ 
% 2.32/0.98  Current options:
% 2.32/0.98  ------ 
% 2.32/0.98  
% 2.32/0.98  ------ Input Options
% 2.32/0.98  
% 2.32/0.98  --out_options                           all
% 2.32/0.98  --tptp_safe_out                         true
% 2.32/0.98  --problem_path                          ""
% 2.32/0.98  --include_path                          ""
% 2.32/0.98  --clausifier                            res/vclausify_rel
% 2.32/0.98  --clausifier_options                    --mode clausify
% 2.32/0.98  --stdin                                 false
% 2.32/0.98  --stats_out                             all
% 2.32/0.98  
% 2.32/0.98  ------ General Options
% 2.32/0.98  
% 2.32/0.98  --fof                                   false
% 2.32/0.98  --time_out_real                         305.
% 2.32/0.98  --time_out_virtual                      -1.
% 2.32/0.98  --symbol_type_check                     false
% 2.32/0.98  --clausify_out                          false
% 2.32/0.98  --sig_cnt_out                           false
% 2.32/0.98  --trig_cnt_out                          false
% 2.32/0.98  --trig_cnt_out_tolerance                1.
% 2.32/0.98  --trig_cnt_out_sk_spl                   false
% 2.32/0.98  --abstr_cl_out                          false
% 2.32/0.98  
% 2.32/0.98  ------ Global Options
% 2.32/0.98  
% 2.32/0.98  --schedule                              default
% 2.32/0.98  --add_important_lit                     false
% 2.32/0.98  --prop_solver_per_cl                    1000
% 2.32/0.98  --min_unsat_core                        false
% 2.32/0.98  --soft_assumptions                      false
% 2.32/0.98  --soft_lemma_size                       3
% 2.32/0.98  --prop_impl_unit_size                   0
% 2.32/0.98  --prop_impl_unit                        []
% 2.32/0.98  --share_sel_clauses                     true
% 2.32/0.98  --reset_solvers                         false
% 2.32/0.98  --bc_imp_inh                            [conj_cone]
% 2.32/0.98  --conj_cone_tolerance                   3.
% 2.32/0.98  --extra_neg_conj                        none
% 2.32/0.98  --large_theory_mode                     true
% 2.32/0.98  --prolific_symb_bound                   200
% 2.32/0.98  --lt_threshold                          2000
% 2.32/0.98  --clause_weak_htbl                      true
% 2.32/0.98  --gc_record_bc_elim                     false
% 2.32/0.98  
% 2.32/0.98  ------ Preprocessing Options
% 2.32/0.98  
% 2.32/0.98  --preprocessing_flag                    true
% 2.32/0.98  --time_out_prep_mult                    0.1
% 2.32/0.98  --splitting_mode                        input
% 2.32/0.98  --splitting_grd                         true
% 2.32/0.98  --splitting_cvd                         false
% 2.32/0.98  --splitting_cvd_svl                     false
% 2.32/0.98  --splitting_nvd                         32
% 2.32/0.98  --sub_typing                            true
% 2.32/0.98  --prep_gs_sim                           true
% 2.32/0.98  --prep_unflatten                        true
% 2.32/0.98  --prep_res_sim                          true
% 2.32/0.98  --prep_upred                            true
% 2.32/0.98  --prep_sem_filter                       exhaustive
% 2.32/0.98  --prep_sem_filter_out                   false
% 2.32/0.98  --pred_elim                             true
% 2.32/0.98  --res_sim_input                         true
% 2.32/0.98  --eq_ax_congr_red                       true
% 2.32/0.98  --pure_diseq_elim                       true
% 2.32/0.98  --brand_transform                       false
% 2.32/0.98  --non_eq_to_eq                          false
% 2.32/0.98  --prep_def_merge                        true
% 2.32/0.98  --prep_def_merge_prop_impl              false
% 2.32/0.98  --prep_def_merge_mbd                    true
% 2.32/0.98  --prep_def_merge_tr_red                 false
% 2.32/0.98  --prep_def_merge_tr_cl                  false
% 2.32/0.98  --smt_preprocessing                     true
% 2.32/0.98  --smt_ac_axioms                         fast
% 2.32/0.98  --preprocessed_out                      false
% 2.32/0.98  --preprocessed_stats                    false
% 2.32/0.98  
% 2.32/0.98  ------ Abstraction refinement Options
% 2.32/0.98  
% 2.32/0.98  --abstr_ref                             []
% 2.32/0.98  --abstr_ref_prep                        false
% 2.32/0.98  --abstr_ref_until_sat                   false
% 2.32/0.98  --abstr_ref_sig_restrict                funpre
% 2.32/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.98  --abstr_ref_under                       []
% 2.32/0.98  
% 2.32/0.98  ------ SAT Options
% 2.32/0.98  
% 2.32/0.98  --sat_mode                              false
% 2.32/0.98  --sat_fm_restart_options                ""
% 2.32/0.98  --sat_gr_def                            false
% 2.32/0.98  --sat_epr_types                         true
% 2.32/0.98  --sat_non_cyclic_types                  false
% 2.32/0.98  --sat_finite_models                     false
% 2.32/0.98  --sat_fm_lemmas                         false
% 2.32/0.98  --sat_fm_prep                           false
% 2.32/0.98  --sat_fm_uc_incr                        true
% 2.32/0.98  --sat_out_model                         small
% 2.32/0.98  --sat_out_clauses                       false
% 2.32/0.98  
% 2.32/0.98  ------ QBF Options
% 2.32/0.98  
% 2.32/0.98  --qbf_mode                              false
% 2.32/0.98  --qbf_elim_univ                         false
% 2.32/0.98  --qbf_dom_inst                          none
% 2.32/0.98  --qbf_dom_pre_inst                      false
% 2.32/0.98  --qbf_sk_in                             false
% 2.32/0.98  --qbf_pred_elim                         true
% 2.32/0.98  --qbf_split                             512
% 2.32/0.98  
% 2.32/0.98  ------ BMC1 Options
% 2.32/0.98  
% 2.32/0.98  --bmc1_incremental                      false
% 2.32/0.98  --bmc1_axioms                           reachable_all
% 2.32/0.98  --bmc1_min_bound                        0
% 2.32/0.98  --bmc1_max_bound                        -1
% 2.32/0.98  --bmc1_max_bound_default                -1
% 2.32/0.98  --bmc1_symbol_reachability              true
% 2.32/0.98  --bmc1_property_lemmas                  false
% 2.32/0.98  --bmc1_k_induction                      false
% 2.32/0.98  --bmc1_non_equiv_states                 false
% 2.32/0.98  --bmc1_deadlock                         false
% 2.32/0.98  --bmc1_ucm                              false
% 2.32/0.98  --bmc1_add_unsat_core                   none
% 2.32/0.98  --bmc1_unsat_core_children              false
% 2.32/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.98  --bmc1_out_stat                         full
% 2.32/0.98  --bmc1_ground_init                      false
% 2.32/0.98  --bmc1_pre_inst_next_state              false
% 2.32/0.98  --bmc1_pre_inst_state                   false
% 2.32/0.98  --bmc1_pre_inst_reach_state             false
% 2.32/0.98  --bmc1_out_unsat_core                   false
% 2.32/0.98  --bmc1_aig_witness_out                  false
% 2.32/0.98  --bmc1_verbose                          false
% 2.32/0.98  --bmc1_dump_clauses_tptp                false
% 2.32/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.98  --bmc1_dump_file                        -
% 2.32/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.98  --bmc1_ucm_extend_mode                  1
% 2.32/0.98  --bmc1_ucm_init_mode                    2
% 2.32/0.98  --bmc1_ucm_cone_mode                    none
% 2.32/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.98  --bmc1_ucm_relax_model                  4
% 2.32/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.98  --bmc1_ucm_layered_model                none
% 2.32/0.98  --bmc1_ucm_max_lemma_size               10
% 2.32/0.98  
% 2.32/0.98  ------ AIG Options
% 2.32/0.98  
% 2.32/0.98  --aig_mode                              false
% 2.32/0.98  
% 2.32/0.98  ------ Instantiation Options
% 2.32/0.98  
% 2.32/0.98  --instantiation_flag                    true
% 2.32/0.98  --inst_sos_flag                         false
% 2.32/0.98  --inst_sos_phase                        true
% 2.32/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.98  --inst_lit_sel_side                     none
% 2.32/0.98  --inst_solver_per_active                1400
% 2.32/0.98  --inst_solver_calls_frac                1.
% 2.32/0.98  --inst_passive_queue_type               priority_queues
% 2.32/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.98  --inst_passive_queues_freq              [25;2]
% 2.32/0.98  --inst_dismatching                      true
% 2.32/0.98  --inst_eager_unprocessed_to_passive     true
% 2.32/0.98  --inst_prop_sim_given                   true
% 2.32/0.98  --inst_prop_sim_new                     false
% 2.32/0.98  --inst_subs_new                         false
% 2.32/0.98  --inst_eq_res_simp                      false
% 2.32/0.98  --inst_subs_given                       false
% 2.32/0.98  --inst_orphan_elimination               true
% 2.32/0.98  --inst_learning_loop_flag               true
% 2.32/0.98  --inst_learning_start                   3000
% 2.32/0.98  --inst_learning_factor                  2
% 2.32/0.98  --inst_start_prop_sim_after_learn       3
% 2.32/0.98  --inst_sel_renew                        solver
% 2.32/0.98  --inst_lit_activity_flag                true
% 2.32/0.98  --inst_restr_to_given                   false
% 2.32/0.98  --inst_activity_threshold               500
% 2.32/0.98  --inst_out_proof                        true
% 2.32/0.98  
% 2.32/0.98  ------ Resolution Options
% 2.32/0.98  
% 2.32/0.98  --resolution_flag                       false
% 2.32/0.98  --res_lit_sel                           adaptive
% 2.32/0.98  --res_lit_sel_side                      none
% 2.32/0.98  --res_ordering                          kbo
% 2.32/0.98  --res_to_prop_solver                    active
% 2.32/0.98  --res_prop_simpl_new                    false
% 2.32/0.98  --res_prop_simpl_given                  true
% 2.32/0.98  --res_passive_queue_type                priority_queues
% 2.32/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/0.98  --res_passive_queues_freq               [15;5]
% 2.32/0.98  --res_forward_subs                      full
% 2.32/0.98  --res_backward_subs                     full
% 2.32/0.98  --res_forward_subs_resolution           true
% 2.32/0.98  --res_backward_subs_resolution          true
% 2.32/0.98  --res_orphan_elimination                true
% 2.32/0.98  --res_time_limit                        2.
% 2.32/0.98  --res_out_proof                         true
% 2.32/0.98  
% 2.32/0.98  ------ Superposition Options
% 2.32/0.98  
% 2.32/0.98  --superposition_flag                    true
% 2.32/0.98  --sup_passive_queue_type                priority_queues
% 2.32/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.32/0.98  --demod_completeness_check              fast
% 2.32/0.98  --demod_use_ground                      true
% 2.32/0.98  --sup_to_prop_solver                    passive
% 2.32/0.98  --sup_prop_simpl_new                    true
% 2.32/0.98  --sup_prop_simpl_given                  true
% 2.32/0.98  --sup_fun_splitting                     false
% 2.32/0.98  --sup_smt_interval                      50000
% 2.32/0.98  
% 2.32/0.98  ------ Superposition Simplification Setup
% 2.32/0.98  
% 2.32/0.98  --sup_indices_passive                   []
% 2.32/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.98  --sup_full_bw                           [BwDemod]
% 2.32/0.98  --sup_immed_triv                        [TrivRules]
% 2.32/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.98  --sup_immed_bw_main                     []
% 2.32/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/0.98  
% 2.32/0.98  ------ Combination Options
% 2.32/0.98  
% 2.32/0.98  --comb_res_mult                         3
% 2.32/0.98  --comb_sup_mult                         2
% 2.32/0.98  --comb_inst_mult                        10
% 2.32/0.98  
% 2.32/0.98  ------ Debug Options
% 2.32/0.98  
% 2.32/0.98  --dbg_backtrace                         false
% 2.32/0.98  --dbg_dump_prop_clauses                 false
% 2.32/0.98  --dbg_dump_prop_clauses_file            -
% 2.32/0.98  --dbg_out_stat                          false
% 2.32/0.98  
% 2.32/0.98  
% 2.32/0.98  
% 2.32/0.98  
% 2.32/0.98  ------ Proving...
% 2.32/0.98  
% 2.32/0.98  
% 2.32/0.98  % SZS status Theorem for theBenchmark.p
% 2.32/0.98  
% 2.32/0.98   Resolution empty clause
% 2.32/0.98  
% 2.32/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/0.98  
% 2.32/0.98  fof(f11,conjecture,(
% 2.32/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f12,negated_conjecture,(
% 2.32/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => (r1_tarski(X5,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 2.32/0.98    inference(negated_conjecture,[],[f11])).
% 2.32/0.98  
% 2.32/0.98  fof(f28,plain,(
% 2.32/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.32/0.98    inference(ennf_transformation,[],[f12])).
% 2.32/0.98  
% 2.32/0.98  fof(f29,plain,(
% 2.32/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/0.98    inference(flattening,[],[f28])).
% 2.32/0.98  
% 2.32/0.98  fof(f35,plain,(
% 2.32/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) => (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,sK5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),sK5) & r1_tarski(sK5,u1_struct_0(X2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X3))))) )),
% 2.32/0.98    introduced(choice_axiom,[])).
% 2.32/0.98  
% 2.32/0.98  fof(f34,plain,(
% 2.32/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),sK4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.32/0.98    introduced(choice_axiom,[])).
% 2.32/0.98  
% 2.32/0.98  fof(f33,plain,(
% 2.32/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.32/0.98    introduced(choice_axiom,[])).
% 2.32/0.98  
% 2.32/0.98  fof(f32,plain,(
% 2.32/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X4),X5) & r1_tarski(X5,u1_struct_0(sK2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.32/0.98    introduced(choice_axiom,[])).
% 2.32/0.98  
% 2.32/0.98  fof(f31,plain,(
% 2.32/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(sK1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.32/0.98    introduced(choice_axiom,[])).
% 2.32/0.98  
% 2.32/0.98  fof(f30,plain,(
% 2.32/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X4),X5) & r1_tarski(X5,u1_struct_0(X2)) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.32/0.98    introduced(choice_axiom,[])).
% 2.32/0.98  
% 2.32/0.98  fof(f36,plain,(
% 2.32/0.98    (((((k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) & r1_tarski(sK5,u1_struct_0(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.32/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f29,f35,f34,f33,f32,f31,f30])).
% 2.32/0.98  
% 2.32/0.98  fof(f62,plain,(
% 2.32/0.98    m1_pre_topc(sK2,sK3)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f61,plain,(
% 2.32/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f8,axiom,(
% 2.32/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f22,plain,(
% 2.32/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/0.98    inference(ennf_transformation,[],[f8])).
% 2.32/0.98  
% 2.32/0.98  fof(f23,plain,(
% 2.32/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.98    inference(flattening,[],[f22])).
% 2.32/0.98  
% 2.32/0.98  fof(f44,plain,(
% 2.32/0.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.98    inference(cnf_transformation,[],[f23])).
% 2.32/0.98  
% 2.32/0.98  fof(f50,plain,(
% 2.32/0.98    v2_pre_topc(sK0)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f51,plain,(
% 2.32/0.98    l1_pre_topc(sK0)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f52,plain,(
% 2.32/0.98    ~v2_struct_0(sK1)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f53,plain,(
% 2.32/0.98    v2_pre_topc(sK1)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f54,plain,(
% 2.32/0.98    l1_pre_topc(sK1)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f57,plain,(
% 2.32/0.98    ~v2_struct_0(sK3)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f58,plain,(
% 2.32/0.98    m1_pre_topc(sK3,sK0)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f59,plain,(
% 2.32/0.98    v1_funct_1(sK4)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f60,plain,(
% 2.32/0.98    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f7,axiom,(
% 2.32/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f21,plain,(
% 2.32/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/0.98    inference(ennf_transformation,[],[f7])).
% 2.32/0.98  
% 2.32/0.98  fof(f43,plain,(
% 2.32/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/0.98    inference(cnf_transformation,[],[f21])).
% 2.32/0.98  
% 2.32/0.98  fof(f5,axiom,(
% 2.32/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f18,plain,(
% 2.32/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/0.98    inference(ennf_transformation,[],[f5])).
% 2.32/0.98  
% 2.32/0.98  fof(f19,plain,(
% 2.32/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/0.98    inference(flattening,[],[f18])).
% 2.32/0.98  
% 2.32/0.98  fof(f41,plain,(
% 2.32/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/0.98    inference(cnf_transformation,[],[f19])).
% 2.32/0.98  
% 2.32/0.98  fof(f4,axiom,(
% 2.32/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f16,plain,(
% 2.32/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.32/0.98    inference(ennf_transformation,[],[f4])).
% 2.32/0.98  
% 2.32/0.98  fof(f17,plain,(
% 2.32/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.32/0.98    inference(flattening,[],[f16])).
% 2.32/0.98  
% 2.32/0.98  fof(f40,plain,(
% 2.32/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.32/0.98    inference(cnf_transformation,[],[f17])).
% 2.32/0.98  
% 2.32/0.98  fof(f10,axiom,(
% 2.32/0.98    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f26,plain,(
% 2.32/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.32/0.98    inference(ennf_transformation,[],[f10])).
% 2.32/0.98  
% 2.32/0.98  fof(f27,plain,(
% 2.32/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.32/0.98    inference(flattening,[],[f26])).
% 2.32/0.98  
% 2.32/0.98  fof(f48,plain,(
% 2.32/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.32/0.98    inference(cnf_transformation,[],[f27])).
% 2.32/0.98  
% 2.32/0.98  fof(f6,axiom,(
% 2.32/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f20,plain,(
% 2.32/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.32/0.98    inference(ennf_transformation,[],[f6])).
% 2.32/0.98  
% 2.32/0.98  fof(f42,plain,(
% 2.32/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.32/0.98    inference(cnf_transformation,[],[f20])).
% 2.32/0.98  
% 2.32/0.98  fof(f3,axiom,(
% 2.32/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f15,plain,(
% 2.32/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.98    inference(ennf_transformation,[],[f3])).
% 2.32/0.98  
% 2.32/0.98  fof(f39,plain,(
% 2.32/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.98    inference(cnf_transformation,[],[f15])).
% 2.32/0.98  
% 2.32/0.98  fof(f56,plain,(
% 2.32/0.98    m1_pre_topc(sK2,sK0)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f9,axiom,(
% 2.32/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f24,plain,(
% 2.32/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/0.98    inference(ennf_transformation,[],[f9])).
% 2.32/0.98  
% 2.32/0.98  fof(f25,plain,(
% 2.32/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/0.98    inference(flattening,[],[f24])).
% 2.32/0.98  
% 2.32/0.98  fof(f45,plain,(
% 2.32/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/0.98    inference(cnf_transformation,[],[f25])).
% 2.32/0.98  
% 2.32/0.98  fof(f49,plain,(
% 2.32/0.98    ~v2_struct_0(sK0)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f65,plain,(
% 2.32/0.98    k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  fof(f2,axiom,(
% 2.32/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f14,plain,(
% 2.32/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/0.98    inference(ennf_transformation,[],[f2])).
% 2.32/0.98  
% 2.32/0.98  fof(f38,plain,(
% 2.32/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/0.98    inference(cnf_transformation,[],[f14])).
% 2.32/0.98  
% 2.32/0.98  fof(f1,axiom,(
% 2.32/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 2.32/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/0.98  
% 2.32/0.98  fof(f13,plain,(
% 2.32/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.32/0.98    inference(ennf_transformation,[],[f1])).
% 2.32/0.98  
% 2.32/0.98  fof(f37,plain,(
% 2.32/0.98    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 2.32/0.98    inference(cnf_transformation,[],[f13])).
% 2.32/0.98  
% 2.32/0.98  fof(f64,plain,(
% 2.32/0.98    r1_tarski(sK5,u1_struct_0(sK2))),
% 2.32/0.98    inference(cnf_transformation,[],[f36])).
% 2.32/0.98  
% 2.32/0.98  cnf(c_15,negated_conjecture,
% 2.32/0.98      ( m1_pre_topc(sK2,sK3) ),
% 2.32/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_514,negated_conjecture,
% 2.32/0.98      ( m1_pre_topc(sK2,sK3) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_983,plain,
% 2.32/0.98      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_16,negated_conjecture,
% 2.32/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.32/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_513,negated_conjecture,
% 2.32/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_984,plain,
% 2.32/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_7,plain,
% 2.32/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/0.98      | ~ m1_pre_topc(X3,X1)
% 2.32/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/0.98      | v2_struct_0(X1)
% 2.32/0.98      | v2_struct_0(X2)
% 2.32/0.98      | ~ l1_pre_topc(X1)
% 2.32/0.98      | ~ l1_pre_topc(X2)
% 2.32/0.98      | ~ v2_pre_topc(X1)
% 2.32/0.98      | ~ v2_pre_topc(X2)
% 2.32/0.98      | ~ v1_funct_1(X0)
% 2.32/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.32/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_521,plain,
% 2.32/0.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 2.32/0.98      | ~ m1_pre_topc(X2_57,X0_57)
% 2.32/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 2.32/0.98      | v2_struct_0(X1_57)
% 2.32/0.98      | v2_struct_0(X0_57)
% 2.32/0.98      | ~ l1_pre_topc(X1_57)
% 2.32/0.98      | ~ l1_pre_topc(X0_57)
% 2.32/0.98      | ~ v2_pre_topc(X1_57)
% 2.32/0.98      | ~ v2_pre_topc(X0_57)
% 2.32/0.98      | ~ v1_funct_1(X0_53)
% 2.32/0.98      | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_53,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_53,X2_57) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_977,plain,
% 2.32/0.98      ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_53,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_53,X2_57)
% 2.32/0.98      | v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 2.32/0.98      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 2.32/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 2.32/0.98      | v2_struct_0(X1_57) = iProver_top
% 2.32/0.98      | v2_struct_0(X0_57) = iProver_top
% 2.32/0.98      | l1_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | l1_pre_topc(X0_57) != iProver_top
% 2.32/0.98      | v2_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | v2_pre_topc(X0_57) != iProver_top
% 2.32/0.98      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2200,plain,
% 2.32/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k2_tmap_1(sK3,sK1,sK4,X0_57)
% 2.32/0.98      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,sK3) != iProver_top
% 2.32/0.98      | v2_struct_0(sK1) = iProver_top
% 2.32/0.98      | v2_struct_0(sK3) = iProver_top
% 2.32/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.32/0.98      | l1_pre_topc(sK3) != iProver_top
% 2.32/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.32/0.98      | v2_pre_topc(sK3) != iProver_top
% 2.32/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_984,c_977]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_27,negated_conjecture,
% 2.32/0.98      ( v2_pre_topc(sK0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_30,plain,
% 2.32/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_26,negated_conjecture,
% 2.32/0.98      ( l1_pre_topc(sK0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_31,plain,
% 2.32/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_25,negated_conjecture,
% 2.32/0.98      ( ~ v2_struct_0(sK1) ),
% 2.32/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_32,plain,
% 2.32/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_24,negated_conjecture,
% 2.32/0.98      ( v2_pre_topc(sK1) ),
% 2.32/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_33,plain,
% 2.32/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_23,negated_conjecture,
% 2.32/0.98      ( l1_pre_topc(sK1) ),
% 2.32/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_34,plain,
% 2.32/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_20,negated_conjecture,
% 2.32/0.98      ( ~ v2_struct_0(sK3) ),
% 2.32/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_37,plain,
% 2.32/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_19,negated_conjecture,
% 2.32/0.98      ( m1_pre_topc(sK3,sK0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_38,plain,
% 2.32/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_18,negated_conjecture,
% 2.32/0.98      ( v1_funct_1(sK4) ),
% 2.32/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_39,plain,
% 2.32/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_17,negated_conjecture,
% 2.32/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.32/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_40,plain,
% 2.32/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_6,plain,
% 2.32/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_522,plain,
% 2.32/0.98      ( ~ m1_pre_topc(X0_57,X1_57)
% 2.32/0.98      | ~ l1_pre_topc(X1_57)
% 2.32/0.98      | l1_pre_topc(X0_57) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1336,plain,
% 2.32/0.98      ( ~ m1_pre_topc(sK3,X0_57) | ~ l1_pre_topc(X0_57) | l1_pre_topc(sK3) ),
% 2.32/0.98      inference(instantiation,[status(thm)],[c_522]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1378,plain,
% 2.32/0.98      ( ~ m1_pre_topc(sK3,sK0) | ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 2.32/0.98      inference(instantiation,[status(thm)],[c_1336]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1379,plain,
% 2.32/0.98      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.32/0.98      | l1_pre_topc(sK0) != iProver_top
% 2.32/0.98      | l1_pre_topc(sK3) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_1378]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_4,plain,
% 2.32/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.32/0.98      | ~ l1_pre_topc(X1)
% 2.32/0.98      | ~ v2_pre_topc(X1)
% 2.32/0.98      | v2_pre_topc(X0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_524,plain,
% 2.32/0.98      ( ~ m1_pre_topc(X0_57,X1_57)
% 2.32/0.98      | ~ l1_pre_topc(X1_57)
% 2.32/0.98      | ~ v2_pre_topc(X1_57)
% 2.32/0.98      | v2_pre_topc(X0_57) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1432,plain,
% 2.32/0.98      ( ~ m1_pre_topc(sK3,X0_57)
% 2.32/0.98      | ~ l1_pre_topc(X0_57)
% 2.32/0.98      | ~ v2_pre_topc(X0_57)
% 2.32/0.98      | v2_pre_topc(sK3) ),
% 2.32/0.98      inference(instantiation,[status(thm)],[c_524]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1578,plain,
% 2.32/0.98      ( ~ m1_pre_topc(sK3,sK0)
% 2.32/0.98      | ~ l1_pre_topc(sK0)
% 2.32/0.98      | ~ v2_pre_topc(sK0)
% 2.32/0.98      | v2_pre_topc(sK3) ),
% 2.32/0.98      inference(instantiation,[status(thm)],[c_1432]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1579,plain,
% 2.32/0.98      ( m1_pre_topc(sK3,sK0) != iProver_top
% 2.32/0.98      | l1_pre_topc(sK0) != iProver_top
% 2.32/0.98      | v2_pre_topc(sK0) != iProver_top
% 2.32/0.98      | v2_pre_topc(sK3) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_1578]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2703,plain,
% 2.32/0.98      ( m1_pre_topc(X0_57,sK3) != iProver_top
% 2.32/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k2_tmap_1(sK3,sK1,sK4,X0_57) ),
% 2.32/0.98      inference(global_propositional_subsumption,
% 2.32/0.98                [status(thm)],
% 2.32/0.98                [c_2200,c_30,c_31,c_32,c_33,c_34,c_37,c_38,c_39,c_40,c_1379,
% 2.32/0.98                 c_1579]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2704,plain,
% 2.32/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k2_tmap_1(sK3,sK1,sK4,X0_57)
% 2.32/0.98      | m1_pre_topc(X0_57,sK3) != iProver_top ),
% 2.32/0.98      inference(renaming,[status(thm)],[c_2703]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3,plain,
% 2.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.98      | ~ v1_funct_1(X0)
% 2.32/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.32/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_525,plain,
% 2.32/0.98      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.32/0.98      | ~ v1_funct_1(X0_53)
% 2.32/0.98      | k2_partfun1(X0_55,X1_55,X0_53,X2_55) = k7_relat_1(X0_53,X2_55) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_973,plain,
% 2.32/0.98      ( k2_partfun1(X0_55,X1_55,X0_53,X2_55) = k7_relat_1(X0_53,X2_55)
% 2.32/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.32/0.98      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1597,plain,
% 2.32/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55)
% 2.32/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_984,c_973]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1235,plain,
% 2.32/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.32/0.98      | ~ v1_funct_1(sK4)
% 2.32/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 2.32/0.98      inference(instantiation,[status(thm)],[c_525]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2630,plain,
% 2.32/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 2.32/0.98      inference(global_propositional_subsumption,
% 2.32/0.98                [status(thm)],
% 2.32/0.98                [c_1597,c_18,c_16,c_1235]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2709,plain,
% 2.32/0.98      ( k2_tmap_1(sK3,sK1,sK4,X0_57) = k7_relat_1(sK4,u1_struct_0(X0_57))
% 2.32/0.98      | m1_pre_topc(X0_57,sK3) != iProver_top ),
% 2.32/0.98      inference(demodulation,[status(thm)],[c_2704,c_2630]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2715,plain,
% 2.32/0.98      ( k2_tmap_1(sK3,sK1,sK4,sK2) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_983,c_2709]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_9,plain,
% 2.32/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/0.98      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 2.32/0.98      | ~ l1_struct_0(X3)
% 2.32/0.98      | ~ l1_struct_0(X2)
% 2.32/0.98      | ~ l1_struct_0(X1)
% 2.32/0.98      | ~ v1_funct_1(X0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_519,plain,
% 2.32/0.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 2.32/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 2.32/0.98      | m1_subset_1(k2_tmap_1(X0_57,X1_57,X0_53,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57))))
% 2.32/0.98      | ~ l1_struct_0(X2_57)
% 2.32/0.98      | ~ l1_struct_0(X1_57)
% 2.32/0.98      | ~ l1_struct_0(X0_57)
% 2.32/0.98      | ~ v1_funct_1(X0_53) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_979,plain,
% 2.32/0.98      ( v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 2.32/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 2.32/0.98      | m1_subset_1(k2_tmap_1(X0_57,X1_57,X0_53,X2_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X1_57)))) = iProver_top
% 2.32/0.98      | l1_struct_0(X2_57) != iProver_top
% 2.32/0.98      | l1_struct_0(X1_57) != iProver_top
% 2.32/0.98      | l1_struct_0(X0_57) != iProver_top
% 2.32/0.98      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2841,plain,
% 2.32/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.32/0.98      | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 2.32/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.32/0.98      | l1_struct_0(sK2) != iProver_top
% 2.32/0.98      | l1_struct_0(sK1) != iProver_top
% 2.32/0.98      | l1_struct_0(sK3) != iProver_top
% 2.32/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_2715,c_979]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_41,plain,
% 2.32/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_5,plain,
% 2.32/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_61,plain,
% 2.32/0.98      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_63,plain,
% 2.32/0.98      ( l1_struct_0(sK1) = iProver_top | l1_pre_topc(sK1) != iProver_top ),
% 2.32/0.98      inference(instantiation,[status(thm)],[c_61]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_523,plain,
% 2.32/0.98      ( l1_struct_0(X0_57) | ~ l1_pre_topc(X0_57) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1331,plain,
% 2.32/0.98      ( l1_struct_0(sK3) | ~ l1_pre_topc(sK3) ),
% 2.32/0.98      inference(instantiation,[status(thm)],[c_523]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1332,plain,
% 2.32/0.98      ( l1_struct_0(sK3) = iProver_top | l1_pre_topc(sK3) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_1331]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_976,plain,
% 2.32/0.98      ( m1_pre_topc(X0_57,X1_57) != iProver_top
% 2.32/0.98      | l1_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | l1_pre_topc(X0_57) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1682,plain,
% 2.32/0.98      ( l1_pre_topc(sK2) = iProver_top | l1_pre_topc(sK3) != iProver_top ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_983,c_976]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1986,plain,
% 2.32/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 2.32/0.98      inference(global_propositional_subsumption,
% 2.32/0.98                [status(thm)],
% 2.32/0.98                [c_1682,c_31,c_38,c_1379]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_975,plain,
% 2.32/0.98      ( l1_struct_0(X0_57) = iProver_top | l1_pre_topc(X0_57) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1991,plain,
% 2.32/0.98      ( l1_struct_0(sK2) = iProver_top ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_1986,c_975]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3246,plain,
% 2.32/0.98      ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.32/0.98      inference(global_propositional_subsumption,
% 2.32/0.98                [status(thm)],
% 2.32/0.98                [c_2841,c_31,c_34,c_38,c_39,c_40,c_41,c_63,c_1332,c_1379,
% 2.32/0.98                 c_1991]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2,plain,
% 2.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.32/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_526,plain,
% 2.32/0.98      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.32/0.98      | k7_relset_1(X0_55,X1_55,X0_53,X1_53) = k9_relat_1(X0_53,X1_53) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_972,plain,
% 2.32/0.98      ( k7_relset_1(X0_55,X1_55,X0_53,X1_53) = k9_relat_1(X0_53,X1_53)
% 2.32/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3253,plain,
% 2.32/0.98      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),X0_53) = k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),X0_53) ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_3246,c_972]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_21,negated_conjecture,
% 2.32/0.98      ( m1_pre_topc(sK2,sK0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_508,negated_conjecture,
% 2.32/0.98      ( m1_pre_topc(sK2,sK0) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_989,plain,
% 2.32/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_510,negated_conjecture,
% 2.32/0.98      ( m1_pre_topc(sK3,sK0) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_987,plain,
% 2.32/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_8,plain,
% 2.32/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/0.98      | ~ m1_pre_topc(X3,X4)
% 2.32/0.98      | ~ m1_pre_topc(X3,X1)
% 2.32/0.98      | ~ m1_pre_topc(X1,X4)
% 2.32/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/0.98      | v2_struct_0(X4)
% 2.32/0.98      | v2_struct_0(X2)
% 2.32/0.98      | ~ l1_pre_topc(X4)
% 2.32/0.98      | ~ l1_pre_topc(X2)
% 2.32/0.98      | ~ v2_pre_topc(X4)
% 2.32/0.98      | ~ v2_pre_topc(X2)
% 2.32/0.98      | ~ v1_funct_1(X0)
% 2.32/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_520,plain,
% 2.32/0.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 2.32/0.98      | ~ m1_pre_topc(X2_57,X3_57)
% 2.32/0.98      | ~ m1_pre_topc(X2_57,X0_57)
% 2.32/0.98      | ~ m1_pre_topc(X0_57,X3_57)
% 2.32/0.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 2.32/0.98      | v2_struct_0(X3_57)
% 2.32/0.98      | v2_struct_0(X1_57)
% 2.32/0.98      | ~ l1_pre_topc(X3_57)
% 2.32/0.98      | ~ l1_pre_topc(X1_57)
% 2.32/0.98      | ~ v2_pre_topc(X3_57)
% 2.32/0.98      | ~ v2_pre_topc(X1_57)
% 2.32/0.98      | ~ v1_funct_1(X0_53)
% 2.32/0.98      | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_53,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_53) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_978,plain,
% 2.32/0.98      ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_53,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_53)
% 2.32/0.98      | v1_funct_2(X0_53,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 2.32/0.98      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 2.32/0.98      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,X3_57) != iProver_top
% 2.32/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 2.32/0.98      | v2_struct_0(X1_57) = iProver_top
% 2.32/0.98      | v2_struct_0(X3_57) = iProver_top
% 2.32/0.98      | l1_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | l1_pre_topc(X3_57) != iProver_top
% 2.32/0.98      | v2_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | v2_pre_topc(X3_57) != iProver_top
% 2.32/0.98      | v1_funct_1(X0_53) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2436,plain,
% 2.32/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK1,sK3,X0_57,sK4)
% 2.32/0.98      | v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,X1_57) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,sK3) != iProver_top
% 2.32/0.98      | m1_pre_topc(sK3,X1_57) != iProver_top
% 2.32/0.98      | v2_struct_0(X1_57) = iProver_top
% 2.32/0.98      | v2_struct_0(sK1) = iProver_top
% 2.32/0.98      | l1_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | l1_pre_topc(sK1) != iProver_top
% 2.32/0.98      | v2_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | v2_pre_topc(sK1) != iProver_top
% 2.32/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_984,c_978]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2880,plain,
% 2.32/0.98      ( l1_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK1,sK3,X0_57,sK4)
% 2.32/0.98      | m1_pre_topc(X0_57,X1_57) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,sK3) != iProver_top
% 2.32/0.98      | m1_pre_topc(sK3,X1_57) != iProver_top
% 2.32/0.98      | v2_struct_0(X1_57) = iProver_top
% 2.32/0.98      | v2_pre_topc(X1_57) != iProver_top ),
% 2.32/0.98      inference(global_propositional_subsumption,
% 2.32/0.98                [status(thm)],
% 2.32/0.98                [c_2436,c_32,c_33,c_34,c_39,c_40]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2881,plain,
% 2.32/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK1,sK3,X0_57,sK4)
% 2.32/0.98      | m1_pre_topc(X0_57,X1_57) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,sK3) != iProver_top
% 2.32/0.98      | m1_pre_topc(sK3,X1_57) != iProver_top
% 2.32/0.98      | v2_struct_0(X1_57) = iProver_top
% 2.32/0.98      | l1_pre_topc(X1_57) != iProver_top
% 2.32/0.98      | v2_pre_topc(X1_57) != iProver_top ),
% 2.32/0.98      inference(renaming,[status(thm)],[c_2880]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2886,plain,
% 2.32/0.98      ( k3_tmap_1(X0_57,sK1,sK3,X1_57,sK4) = k7_relat_1(sK4,u1_struct_0(X1_57))
% 2.32/0.98      | m1_pre_topc(X1_57,X0_57) != iProver_top
% 2.32/0.98      | m1_pre_topc(X1_57,sK3) != iProver_top
% 2.32/0.98      | m1_pre_topc(sK3,X0_57) != iProver_top
% 2.32/0.98      | v2_struct_0(X0_57) = iProver_top
% 2.32/0.98      | l1_pre_topc(X0_57) != iProver_top
% 2.32/0.98      | v2_pre_topc(X0_57) != iProver_top ),
% 2.32/0.98      inference(demodulation,[status(thm)],[c_2881,c_2630]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_2897,plain,
% 2.32/0.98      ( k3_tmap_1(sK0,sK1,sK3,X0_57,sK4) = k7_relat_1(sK4,u1_struct_0(X0_57))
% 2.32/0.98      | m1_pre_topc(X0_57,sK0) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,sK3) != iProver_top
% 2.32/0.98      | v2_struct_0(sK0) = iProver_top
% 2.32/0.98      | l1_pre_topc(sK0) != iProver_top
% 2.32/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_987,c_2886]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_28,negated_conjecture,
% 2.32/0.98      ( ~ v2_struct_0(sK0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_29,plain,
% 2.32/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3046,plain,
% 2.32/0.98      ( m1_pre_topc(X0_57,sK3) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,sK0) != iProver_top
% 2.32/0.98      | k3_tmap_1(sK0,sK1,sK3,X0_57,sK4) = k7_relat_1(sK4,u1_struct_0(X0_57)) ),
% 2.32/0.98      inference(global_propositional_subsumption,
% 2.32/0.98                [status(thm)],
% 2.32/0.98                [c_2897,c_29,c_30,c_31]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3047,plain,
% 2.32/0.98      ( k3_tmap_1(sK0,sK1,sK3,X0_57,sK4) = k7_relat_1(sK4,u1_struct_0(X0_57))
% 2.32/0.98      | m1_pre_topc(X0_57,sK0) != iProver_top
% 2.32/0.98      | m1_pre_topc(X0_57,sK3) != iProver_top ),
% 2.32/0.98      inference(renaming,[status(thm)],[c_3046]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3056,plain,
% 2.32/0.98      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))
% 2.32/0.98      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_989,c_3047]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_42,plain,
% 2.32/0.98      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3119,plain,
% 2.32/0.98      ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
% 2.32/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3056,c_42]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1525,plain,
% 2.32/0.98      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0_53) = k9_relat_1(sK4,X0_53) ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_984,c_972]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_12,negated_conjecture,
% 2.32/0.98      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 2.32/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_516,negated_conjecture,
% 2.32/0.98      ( k7_relset_1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1528,plain,
% 2.32/0.98      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k9_relat_1(sK4,sK5) ),
% 2.32/0.98      inference(demodulation,[status(thm)],[c_1525,c_516]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3122,plain,
% 2.32/0.98      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 2.32/0.98      inference(demodulation,[status(thm)],[c_3119,c_1528]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3336,plain,
% 2.32/0.98      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k9_relat_1(sK4,sK5) ),
% 2.32/0.98      inference(demodulation,[status(thm)],[c_3253,c_3122]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1,plain,
% 2.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_0,plain,
% 2.32/0.98      ( ~ r1_tarski(X0,X1)
% 2.32/0.98      | ~ v1_relat_1(X2)
% 2.32/0.98      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 2.32/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_13,negated_conjecture,
% 2.32/0.98      ( r1_tarski(sK5,u1_struct_0(sK2)) ),
% 2.32/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_294,plain,
% 2.32/0.98      ( ~ v1_relat_1(X0)
% 2.32/0.98      | k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 2.32/0.98      | u1_struct_0(sK2) != X1
% 2.32/0.98      | sK5 != X2 ),
% 2.32/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_13]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_295,plain,
% 2.32/0.98      ( ~ v1_relat_1(X0)
% 2.32/0.98      | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
% 2.32/0.98      inference(unflattening,[status(thm)],[c_294]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_309,plain,
% 2.32/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/0.98      | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k9_relat_1(X0,sK5) ),
% 2.32/0.98      inference(resolution,[status(thm)],[c_1,c_295]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_500,plain,
% 2.32/0.98      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.32/0.98      | k9_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_53,sK5) ),
% 2.32/0.98      inference(subtyping,[status(esa)],[c_309]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_997,plain,
% 2.32/0.98      ( k9_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),sK5) = k9_relat_1(X0_53,sK5)
% 2.32/0.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.32/0.98      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_1577,plain,
% 2.32/0.98      ( k9_relat_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k9_relat_1(sK4,sK5) ),
% 2.32/0.98      inference(superposition,[status(thm)],[c_984,c_997]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3337,plain,
% 2.32/0.98      ( k9_relat_1(sK4,sK5) != k9_relat_1(sK4,sK5) ),
% 2.32/0.98      inference(light_normalisation,[status(thm)],[c_3336,c_1577]) ).
% 2.32/0.98  
% 2.32/0.98  cnf(c_3338,plain,
% 2.32/0.98      ( $false ),
% 2.32/0.98      inference(equality_resolution_simp,[status(thm)],[c_3337]) ).
% 2.32/0.98  
% 2.32/0.98  
% 2.32/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/0.98  
% 2.32/0.98  ------                               Statistics
% 2.32/0.98  
% 2.32/0.98  ------ General
% 2.32/0.98  
% 2.32/0.98  abstr_ref_over_cycles:                  0
% 2.32/0.98  abstr_ref_under_cycles:                 0
% 2.32/0.98  gc_basic_clause_elim:                   0
% 2.32/0.98  forced_gc_time:                         0
% 2.32/0.98  parsing_time:                           0.009
% 2.32/0.98  unif_index_cands_time:                  0.
% 2.32/0.98  unif_index_add_time:                    0.
% 2.32/0.98  orderings_time:                         0.
% 2.32/0.98  out_proof_time:                         0.01
% 2.32/0.98  total_time:                             0.204
% 2.32/0.98  num_of_symbols:                         61
% 2.32/0.98  num_of_terms:                           3304
% 2.32/0.98  
% 2.32/0.98  ------ Preprocessing
% 2.32/0.98  
% 2.32/0.98  num_of_splits:                          0
% 2.32/0.98  num_of_split_atoms:                     0
% 2.32/0.98  num_of_reused_defs:                     0
% 2.32/0.98  num_eq_ax_congr_red:                    46
% 2.32/0.98  num_of_sem_filtered_clauses:            1
% 2.32/0.98  num_of_subtypes:                        5
% 2.32/0.98  monotx_restored_types:                  0
% 2.32/0.98  sat_num_of_epr_types:                   0
% 2.32/0.98  sat_num_of_non_cyclic_types:            0
% 2.32/0.98  sat_guarded_non_collapsed_types:        0
% 2.32/0.98  num_pure_diseq_elim:                    0
% 2.32/0.98  simp_replaced_by:                       0
% 2.32/0.98  res_preprocessed:                       131
% 2.32/0.98  prep_upred:                             0
% 2.32/0.98  prep_unflattend:                        2
% 2.32/0.98  smt_new_axioms:                         0
% 2.32/0.98  pred_elim_cands:                        8
% 2.32/0.98  pred_elim:                              2
% 2.32/0.98  pred_elim_cl:                           2
% 2.32/0.98  pred_elim_cycles:                       4
% 2.32/0.98  merged_defs:                            0
% 2.32/0.98  merged_defs_ncl:                        0
% 2.32/0.98  bin_hyper_res:                          0
% 2.32/0.98  prep_cycles:                            4
% 2.32/0.98  pred_elim_time:                         0.001
% 2.32/0.98  splitting_time:                         0.
% 2.32/0.98  sem_filter_time:                        0.
% 2.32/0.98  monotx_time:                            0.
% 2.32/0.98  subtype_inf_time:                       0.
% 2.32/0.98  
% 2.32/0.98  ------ Problem properties
% 2.32/0.98  
% 2.32/0.98  clauses:                                27
% 2.32/0.98  conjectures:                            16
% 2.32/0.98  epr:                                    15
% 2.32/0.98  horn:                                   25
% 2.32/0.98  ground:                                 16
% 2.32/0.98  unary:                                  16
% 2.32/0.98  binary:                                 3
% 2.32/0.98  lits:                                   77
% 2.32/0.98  lits_eq:                                6
% 2.32/0.98  fd_pure:                                0
% 2.32/0.98  fd_pseudo:                              0
% 2.32/0.98  fd_cond:                                0
% 2.32/0.98  fd_pseudo_cond:                         0
% 2.32/0.98  ac_symbols:                             0
% 2.32/0.98  
% 2.32/0.98  ------ Propositional Solver
% 2.32/0.98  
% 2.32/0.98  prop_solver_calls:                      30
% 2.32/0.98  prop_fast_solver_calls:                 919
% 2.32/0.98  smt_solver_calls:                       0
% 2.32/0.98  smt_fast_solver_calls:                  0
% 2.32/0.98  prop_num_of_clauses:                    1002
% 2.32/0.98  prop_preprocess_simplified:             4341
% 2.32/0.98  prop_fo_subsumed:                       43
% 2.32/0.98  prop_solver_time:                       0.
% 2.32/0.98  smt_solver_time:                        0.
% 2.32/0.98  smt_fast_solver_time:                   0.
% 2.32/0.98  prop_fast_solver_time:                  0.
% 2.32/0.98  prop_unsat_core_time:                   0.
% 2.32/0.98  
% 2.32/0.98  ------ QBF
% 2.32/0.98  
% 2.32/0.98  qbf_q_res:                              0
% 2.32/0.98  qbf_num_tautologies:                    0
% 2.32/0.98  qbf_prep_cycles:                        0
% 2.32/0.98  
% 2.32/0.98  ------ BMC1
% 2.32/0.98  
% 2.32/0.98  bmc1_current_bound:                     -1
% 2.32/0.98  bmc1_last_solved_bound:                 -1
% 2.32/0.98  bmc1_unsat_core_size:                   -1
% 2.32/0.98  bmc1_unsat_core_parents_size:           -1
% 2.32/0.98  bmc1_merge_next_fun:                    0
% 2.32/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.32/0.98  
% 2.32/0.98  ------ Instantiation
% 2.32/0.98  
% 2.32/0.98  inst_num_of_clauses:                    341
% 2.32/0.98  inst_num_in_passive:                    95
% 2.32/0.98  inst_num_in_active:                     215
% 2.32/0.98  inst_num_in_unprocessed:                31
% 2.32/0.98  inst_num_of_loops:                      250
% 2.32/0.98  inst_num_of_learning_restarts:          0
% 2.32/0.98  inst_num_moves_active_passive:          30
% 2.32/0.98  inst_lit_activity:                      0
% 2.32/0.98  inst_lit_activity_moves:                0
% 2.32/0.98  inst_num_tautologies:                   0
% 2.32/0.98  inst_num_prop_implied:                  0
% 2.32/0.98  inst_num_existing_simplified:           0
% 2.32/0.98  inst_num_eq_res_simplified:             0
% 2.32/0.98  inst_num_child_elim:                    0
% 2.32/0.98  inst_num_of_dismatching_blockings:      75
% 2.32/0.98  inst_num_of_non_proper_insts:           334
% 2.32/0.98  inst_num_of_duplicates:                 0
% 2.32/0.98  inst_inst_num_from_inst_to_res:         0
% 2.32/0.98  inst_dismatching_checking_time:         0.
% 2.32/0.98  
% 2.32/0.98  ------ Resolution
% 2.32/0.98  
% 2.32/0.98  res_num_of_clauses:                     0
% 2.32/0.98  res_num_in_passive:                     0
% 2.32/0.98  res_num_in_active:                      0
% 2.32/0.98  res_num_of_loops:                       135
% 2.32/0.98  res_forward_subset_subsumed:            32
% 2.32/0.98  res_backward_subset_subsumed:           0
% 2.32/0.98  res_forward_subsumed:                   0
% 2.32/0.98  res_backward_subsumed:                  0
% 2.32/0.98  res_forward_subsumption_resolution:     0
% 2.32/0.98  res_backward_subsumption_resolution:    0
% 2.32/0.98  res_clause_to_clause_subsumption:       93
% 2.32/0.98  res_orphan_elimination:                 0
% 2.32/0.98  res_tautology_del:                      36
% 2.32/0.98  res_num_eq_res_simplified:              0
% 2.32/0.98  res_num_sel_changes:                    0
% 2.32/0.98  res_moves_from_active_to_pass:          0
% 2.32/0.98  
% 2.32/0.98  ------ Superposition
% 2.32/0.98  
% 2.32/0.98  sup_time_total:                         0.
% 2.32/0.98  sup_time_generating:                    0.
% 2.32/0.98  sup_time_sim_full:                      0.
% 2.32/0.98  sup_time_sim_immed:                     0.
% 2.32/0.98  
% 2.32/0.98  sup_num_of_clauses:                     59
% 2.32/0.98  sup_num_in_active:                      46
% 2.32/0.98  sup_num_in_passive:                     13
% 2.32/0.98  sup_num_of_loops:                       49
% 2.32/0.98  sup_fw_superposition:                   18
% 2.32/0.98  sup_bw_superposition:                   17
% 2.32/0.98  sup_immediate_simplified:               1
% 2.32/0.98  sup_given_eliminated:                   0
% 2.32/0.98  comparisons_done:                       0
% 2.32/0.98  comparisons_avoided:                    0
% 2.32/0.98  
% 2.32/0.98  ------ Simplifications
% 2.32/0.98  
% 2.32/0.98  
% 2.32/0.98  sim_fw_subset_subsumed:                 0
% 2.32/0.98  sim_bw_subset_subsumed:                 0
% 2.32/0.98  sim_fw_subsumed:                        0
% 2.32/0.98  sim_bw_subsumed:                        0
% 2.32/0.98  sim_fw_subsumption_res:                 0
% 2.32/0.98  sim_bw_subsumption_res:                 0
% 2.32/0.98  sim_tautology_del:                      0
% 2.32/0.98  sim_eq_tautology_del:                   0
% 2.32/0.98  sim_eq_res_simp:                        0
% 2.32/0.98  sim_fw_demodulated:                     2
% 2.32/0.98  sim_bw_demodulated:                     3
% 2.32/0.98  sim_light_normalised:                   2
% 2.32/0.98  sim_joinable_taut:                      0
% 2.32/0.98  sim_joinable_simp:                      0
% 2.32/0.98  sim_ac_normalised:                      0
% 2.32/0.98  sim_smt_subsumption:                    0
% 2.32/0.98  
%------------------------------------------------------------------------------
