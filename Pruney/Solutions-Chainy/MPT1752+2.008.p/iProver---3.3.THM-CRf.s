%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:36 EST 2020

% Result     : Theorem 15.49s
% Output     : CNFRefutation 15.49s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 507 expanded)
%              Number of clauses        :  108 ( 181 expanded)
%              Number of leaves         :   19 ( 156 expanded)
%              Depth                    :   25
%              Number of atoms          :  610 (3956 expanded)
%              Number of equality atoms :  154 ( 494 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                       => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
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
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
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
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4)
        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
              & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),X4)
            & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),u1_struct_0(X2))
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                  & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),X4)
                & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(sK2))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),X4)
                    & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
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
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
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
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f41,f40,f39,f38,f37])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK0) ),
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

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1332,plain,
    ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1790,plain,
    ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1332])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1326,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1795,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1335,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1787,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | r1_tarski(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1335])).

cnf(c_2214,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1787])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1337,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | ~ r1_tarski(X2_53,X0_53)
    | r1_tarski(X2_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1785,plain,
    ( r1_tarski(X0_53,X1_53) != iProver_top
    | r1_tarski(X2_53,X0_53) != iProver_top
    | r1_tarski(X2_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1337])).

cnf(c_2360,plain,
    ( r1_tarski(X0_53,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top
    | r1_tarski(X0_53,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2214,c_1785])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1336,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ r1_tarski(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1786,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) = iProver_top
    | r1_tarski(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1336])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_5])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | r1_tarski(k2_relat_1(X0_53),X2_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_1797,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_4248,plain,
    ( r1_tarski(X0_53,k2_zfmisc_1(X1_53,X2_53)) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_1797])).

cnf(c_7141,plain,
    ( r1_tarski(X0_53,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_4248])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1334,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2298,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_2299,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2298])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_204,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_257,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_204])).

cnf(c_1325,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_257])).

cnf(c_1796,plain,
    ( r1_tarski(X0_53,X1_53) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_3316,plain,
    ( r1_tarski(X0_53,sK3) != iProver_top
    | v1_relat_1(X0_53) = iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_1796])).

cnf(c_7343,plain,
    ( r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0_53,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7141,c_2299,c_3316])).

cnf(c_7344,plain,
    ( r1_tarski(X0_53,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7343])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1333,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1789,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1330,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ r1_tarski(k1_relat_1(X0_53),X1_53)
    | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1792,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
    | r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1331,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1791,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1331])).

cnf(c_2712,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
    | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1792,c_1791])).

cnf(c_7999,plain,
    ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top
    | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_2712])).

cnf(c_3313,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1796])).

cnf(c_50556,plain,
    ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7999,c_3313])).

cnf(c_50570,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(X1_53,X0_53),X2_53) = k10_relat_1(k7_relat_1(X1_53,X0_53),X2_53)
    | r1_tarski(k7_relat_1(X1_53,X0_53),sK3) != iProver_top
    | v1_relat_1(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_7344,c_50556])).

cnf(c_51795,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_50570])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1936,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_1937,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_1918,plain,
    ( ~ r1_tarski(X0_53,k2_zfmisc_1(X1_53,X2_53))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_2245,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_2246,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2245])).

cnf(c_53500,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51795,c_39,c_1937,c_2246,c_2299])).

cnf(c_2693,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_1795,c_1791])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_475,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_1322,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
    inference(subtyping,[status(esa)],[c_475])).

cnf(c_1799,plain,
    ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_1994,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_1795,c_1799])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_381,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK2 != X3
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_382,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_386,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_28,c_27,c_26])).

cnf(c_387,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_386])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_387])).

cnf(c_423,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_427,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_20])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_427])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_493,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_428,c_23])).

cnf(c_494,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_496,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_25,c_24,c_18])).

cnf(c_877,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_496])).

cnf(c_1320,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_877])).

cnf(c_2033,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_1994,c_1320])).

cnf(c_15,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1329,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2440,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2033,c_1329])).

cnf(c_2874,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2693,c_2440])).

cnf(c_53504,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_53500,c_2874])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1328,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1793,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_2876,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2693,c_1793])).

cnf(c_13,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_459,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_460,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_1323,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0_53),X1_53)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X1_53),X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(subtyping,[status(esa)],[c_460])).

cnf(c_1798,plain,
    ( k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(sK3,X1_53)
    | r1_tarski(k10_relat_1(sK3,X1_53),X0_53) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_2892,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_1798])).

cnf(c_3116,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2892,c_39,c_1937,c_2246,c_2299])).

cnf(c_53505,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_53504,c_3116])).

cnf(c_53506,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_53505])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:41:38 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 15.49/2.55  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.49/2.55  
% 15.49/2.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.49/2.55  
% 15.49/2.55  ------  iProver source info
% 15.49/2.55  
% 15.49/2.55  git: date: 2020-06-30 10:37:57 +0100
% 15.49/2.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.49/2.55  git: non_committed_changes: false
% 15.49/2.55  git: last_make_outside_of_git: false
% 15.49/2.55  
% 15.49/2.55  ------ 
% 15.49/2.55  
% 15.49/2.55  ------ Input Options
% 15.49/2.55  
% 15.49/2.55  --out_options                           all
% 15.49/2.55  --tptp_safe_out                         true
% 15.49/2.55  --problem_path                          ""
% 15.49/2.55  --include_path                          ""
% 15.49/2.55  --clausifier                            res/vclausify_rel
% 15.49/2.55  --clausifier_options                    --mode clausify
% 15.49/2.55  --stdin                                 false
% 15.49/2.55  --stats_out                             all
% 15.49/2.55  
% 15.49/2.55  ------ General Options
% 15.49/2.55  
% 15.49/2.55  --fof                                   false
% 15.49/2.55  --time_out_real                         305.
% 15.49/2.55  --time_out_virtual                      -1.
% 15.49/2.55  --symbol_type_check                     false
% 15.49/2.55  --clausify_out                          false
% 15.49/2.55  --sig_cnt_out                           false
% 15.49/2.55  --trig_cnt_out                          false
% 15.49/2.55  --trig_cnt_out_tolerance                1.
% 15.49/2.55  --trig_cnt_out_sk_spl                   false
% 15.49/2.55  --abstr_cl_out                          false
% 15.49/2.55  
% 15.49/2.55  ------ Global Options
% 15.49/2.55  
% 15.49/2.55  --schedule                              default
% 15.49/2.55  --add_important_lit                     false
% 15.49/2.55  --prop_solver_per_cl                    1000
% 15.49/2.55  --min_unsat_core                        false
% 15.49/2.55  --soft_assumptions                      false
% 15.49/2.55  --soft_lemma_size                       3
% 15.49/2.55  --prop_impl_unit_size                   0
% 15.49/2.55  --prop_impl_unit                        []
% 15.49/2.55  --share_sel_clauses                     true
% 15.49/2.55  --reset_solvers                         false
% 15.49/2.55  --bc_imp_inh                            [conj_cone]
% 15.49/2.55  --conj_cone_tolerance                   3.
% 15.49/2.55  --extra_neg_conj                        none
% 15.49/2.55  --large_theory_mode                     true
% 15.49/2.55  --prolific_symb_bound                   200
% 15.49/2.55  --lt_threshold                          2000
% 15.49/2.55  --clause_weak_htbl                      true
% 15.49/2.55  --gc_record_bc_elim                     false
% 15.49/2.55  
% 15.49/2.55  ------ Preprocessing Options
% 15.49/2.55  
% 15.49/2.55  --preprocessing_flag                    true
% 15.49/2.55  --time_out_prep_mult                    0.1
% 15.49/2.55  --splitting_mode                        input
% 15.49/2.55  --splitting_grd                         true
% 15.49/2.55  --splitting_cvd                         false
% 15.49/2.55  --splitting_cvd_svl                     false
% 15.49/2.55  --splitting_nvd                         32
% 15.49/2.55  --sub_typing                            true
% 15.49/2.55  --prep_gs_sim                           true
% 15.49/2.55  --prep_unflatten                        true
% 15.49/2.55  --prep_res_sim                          true
% 15.49/2.55  --prep_upred                            true
% 15.49/2.55  --prep_sem_filter                       exhaustive
% 15.49/2.55  --prep_sem_filter_out                   false
% 15.49/2.55  --pred_elim                             true
% 15.49/2.55  --res_sim_input                         true
% 15.49/2.55  --eq_ax_congr_red                       true
% 15.49/2.55  --pure_diseq_elim                       true
% 15.49/2.55  --brand_transform                       false
% 15.49/2.55  --non_eq_to_eq                          false
% 15.49/2.55  --prep_def_merge                        true
% 15.49/2.55  --prep_def_merge_prop_impl              false
% 15.49/2.55  --prep_def_merge_mbd                    true
% 15.49/2.55  --prep_def_merge_tr_red                 false
% 15.49/2.55  --prep_def_merge_tr_cl                  false
% 15.49/2.55  --smt_preprocessing                     true
% 15.49/2.55  --smt_ac_axioms                         fast
% 15.49/2.55  --preprocessed_out                      false
% 15.49/2.55  --preprocessed_stats                    false
% 15.49/2.55  
% 15.49/2.55  ------ Abstraction refinement Options
% 15.49/2.55  
% 15.49/2.55  --abstr_ref                             []
% 15.49/2.55  --abstr_ref_prep                        false
% 15.49/2.55  --abstr_ref_until_sat                   false
% 15.49/2.55  --abstr_ref_sig_restrict                funpre
% 15.49/2.55  --abstr_ref_af_restrict_to_split_sk     false
% 15.49/2.55  --abstr_ref_under                       []
% 15.49/2.55  
% 15.49/2.55  ------ SAT Options
% 15.49/2.55  
% 15.49/2.55  --sat_mode                              false
% 15.49/2.55  --sat_fm_restart_options                ""
% 15.49/2.55  --sat_gr_def                            false
% 15.49/2.55  --sat_epr_types                         true
% 15.49/2.55  --sat_non_cyclic_types                  false
% 15.49/2.55  --sat_finite_models                     false
% 15.49/2.55  --sat_fm_lemmas                         false
% 15.49/2.55  --sat_fm_prep                           false
% 15.49/2.55  --sat_fm_uc_incr                        true
% 15.49/2.55  --sat_out_model                         small
% 15.49/2.55  --sat_out_clauses                       false
% 15.49/2.55  
% 15.49/2.55  ------ QBF Options
% 15.49/2.55  
% 15.49/2.55  --qbf_mode                              false
% 15.49/2.55  --qbf_elim_univ                         false
% 15.49/2.55  --qbf_dom_inst                          none
% 15.49/2.55  --qbf_dom_pre_inst                      false
% 15.49/2.55  --qbf_sk_in                             false
% 15.49/2.55  --qbf_pred_elim                         true
% 15.49/2.55  --qbf_split                             512
% 15.49/2.55  
% 15.49/2.55  ------ BMC1 Options
% 15.49/2.55  
% 15.49/2.55  --bmc1_incremental                      false
% 15.49/2.55  --bmc1_axioms                           reachable_all
% 15.49/2.55  --bmc1_min_bound                        0
% 15.49/2.55  --bmc1_max_bound                        -1
% 15.49/2.55  --bmc1_max_bound_default                -1
% 15.49/2.55  --bmc1_symbol_reachability              true
% 15.49/2.55  --bmc1_property_lemmas                  false
% 15.49/2.55  --bmc1_k_induction                      false
% 15.49/2.55  --bmc1_non_equiv_states                 false
% 15.49/2.55  --bmc1_deadlock                         false
% 15.49/2.55  --bmc1_ucm                              false
% 15.49/2.55  --bmc1_add_unsat_core                   none
% 15.49/2.55  --bmc1_unsat_core_children              false
% 15.49/2.55  --bmc1_unsat_core_extrapolate_axioms    false
% 15.49/2.55  --bmc1_out_stat                         full
% 15.49/2.55  --bmc1_ground_init                      false
% 15.49/2.55  --bmc1_pre_inst_next_state              false
% 15.49/2.55  --bmc1_pre_inst_state                   false
% 15.49/2.55  --bmc1_pre_inst_reach_state             false
% 15.49/2.55  --bmc1_out_unsat_core                   false
% 15.49/2.55  --bmc1_aig_witness_out                  false
% 15.49/2.55  --bmc1_verbose                          false
% 15.49/2.55  --bmc1_dump_clauses_tptp                false
% 15.49/2.55  --bmc1_dump_unsat_core_tptp             false
% 15.49/2.55  --bmc1_dump_file                        -
% 15.49/2.55  --bmc1_ucm_expand_uc_limit              128
% 15.49/2.55  --bmc1_ucm_n_expand_iterations          6
% 15.49/2.55  --bmc1_ucm_extend_mode                  1
% 15.49/2.55  --bmc1_ucm_init_mode                    2
% 15.49/2.55  --bmc1_ucm_cone_mode                    none
% 15.49/2.55  --bmc1_ucm_reduced_relation_type        0
% 15.49/2.55  --bmc1_ucm_relax_model                  4
% 15.49/2.55  --bmc1_ucm_full_tr_after_sat            true
% 15.49/2.55  --bmc1_ucm_expand_neg_assumptions       false
% 15.49/2.55  --bmc1_ucm_layered_model                none
% 15.49/2.55  --bmc1_ucm_max_lemma_size               10
% 15.49/2.55  
% 15.49/2.55  ------ AIG Options
% 15.49/2.55  
% 15.49/2.55  --aig_mode                              false
% 15.49/2.55  
% 15.49/2.55  ------ Instantiation Options
% 15.49/2.55  
% 15.49/2.55  --instantiation_flag                    true
% 15.49/2.55  --inst_sos_flag                         false
% 15.49/2.55  --inst_sos_phase                        true
% 15.49/2.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.49/2.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.49/2.55  --inst_lit_sel_side                     num_symb
% 15.49/2.55  --inst_solver_per_active                1400
% 15.49/2.55  --inst_solver_calls_frac                1.
% 15.49/2.55  --inst_passive_queue_type               priority_queues
% 15.49/2.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.49/2.55  --inst_passive_queues_freq              [25;2]
% 15.49/2.55  --inst_dismatching                      true
% 15.49/2.55  --inst_eager_unprocessed_to_passive     true
% 15.49/2.55  --inst_prop_sim_given                   true
% 15.49/2.55  --inst_prop_sim_new                     false
% 15.49/2.55  --inst_subs_new                         false
% 15.49/2.55  --inst_eq_res_simp                      false
% 15.49/2.55  --inst_subs_given                       false
% 15.49/2.55  --inst_orphan_elimination               true
% 15.49/2.55  --inst_learning_loop_flag               true
% 15.49/2.55  --inst_learning_start                   3000
% 15.49/2.55  --inst_learning_factor                  2
% 15.49/2.55  --inst_start_prop_sim_after_learn       3
% 15.49/2.55  --inst_sel_renew                        solver
% 15.49/2.55  --inst_lit_activity_flag                true
% 15.49/2.55  --inst_restr_to_given                   false
% 15.49/2.55  --inst_activity_threshold               500
% 15.49/2.55  --inst_out_proof                        true
% 15.49/2.55  
% 15.49/2.55  ------ Resolution Options
% 15.49/2.55  
% 15.49/2.55  --resolution_flag                       true
% 15.49/2.55  --res_lit_sel                           adaptive
% 15.49/2.55  --res_lit_sel_side                      none
% 15.49/2.55  --res_ordering                          kbo
% 15.49/2.55  --res_to_prop_solver                    active
% 15.49/2.55  --res_prop_simpl_new                    false
% 15.49/2.55  --res_prop_simpl_given                  true
% 15.49/2.55  --res_passive_queue_type                priority_queues
% 15.49/2.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.49/2.55  --res_passive_queues_freq               [15;5]
% 15.49/2.55  --res_forward_subs                      full
% 15.49/2.55  --res_backward_subs                     full
% 15.49/2.55  --res_forward_subs_resolution           true
% 15.49/2.55  --res_backward_subs_resolution          true
% 15.49/2.55  --res_orphan_elimination                true
% 15.49/2.55  --res_time_limit                        2.
% 15.49/2.55  --res_out_proof                         true
% 15.49/2.55  
% 15.49/2.55  ------ Superposition Options
% 15.49/2.55  
% 15.49/2.55  --superposition_flag                    true
% 15.49/2.55  --sup_passive_queue_type                priority_queues
% 15.49/2.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.49/2.55  --sup_passive_queues_freq               [8;1;4]
% 15.49/2.55  --demod_completeness_check              fast
% 15.49/2.55  --demod_use_ground                      true
% 15.49/2.55  --sup_to_prop_solver                    passive
% 15.49/2.55  --sup_prop_simpl_new                    true
% 15.49/2.55  --sup_prop_simpl_given                  true
% 15.49/2.55  --sup_fun_splitting                     false
% 15.49/2.55  --sup_smt_interval                      50000
% 15.49/2.55  
% 15.49/2.55  ------ Superposition Simplification Setup
% 15.49/2.55  
% 15.49/2.55  --sup_indices_passive                   []
% 15.49/2.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.55  --sup_full_triv                         [TrivRules;PropSubs]
% 15.49/2.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.49/2.55  --sup_full_bw                           [BwDemod]
% 15.49/2.55  --sup_immed_triv                        [TrivRules]
% 15.49/2.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.49/2.55  --sup_immed_bw_main                     []
% 15.49/2.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.49/2.55  --sup_input_triv                        [Unflattening;TrivRules]
% 15.49/2.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.49/2.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.49/2.55  
% 15.49/2.55  ------ Combination Options
% 15.49/2.55  
% 15.49/2.55  --comb_res_mult                         3
% 15.49/2.55  --comb_sup_mult                         2
% 15.49/2.55  --comb_inst_mult                        10
% 15.49/2.55  
% 15.49/2.55  ------ Debug Options
% 15.49/2.55  
% 15.49/2.55  --dbg_backtrace                         false
% 15.49/2.55  --dbg_dump_prop_clauses                 false
% 15.49/2.55  --dbg_dump_prop_clauses_file            -
% 15.49/2.55  --dbg_out_stat                          false
% 15.49/2.55  ------ Parsing...
% 15.49/2.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.49/2.55  
% 15.49/2.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 15.49/2.55  
% 15.49/2.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.49/2.55  
% 15.49/2.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.49/2.55  ------ Proving...
% 15.49/2.55  ------ Problem Properties 
% 15.49/2.55  
% 15.49/2.55  
% 15.49/2.55  clauses                                 18
% 15.49/2.55  conjectures                             4
% 15.49/2.55  EPR                                     2
% 15.49/2.55  Horn                                    18
% 15.49/2.55  unary                                   6
% 15.49/2.55  binary                                  6
% 15.49/2.55  lits                                    37
% 15.49/2.55  lits eq                                 7
% 15.49/2.55  fd_pure                                 0
% 15.49/2.55  fd_pseudo                               0
% 15.49/2.55  fd_cond                                 0
% 15.49/2.55  fd_pseudo_cond                          0
% 15.49/2.55  AC symbols                              0
% 15.49/2.55  
% 15.49/2.55  ------ Schedule dynamic 5 is on 
% 15.49/2.55  
% 15.49/2.55  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.49/2.55  
% 15.49/2.55  
% 15.49/2.55  ------ 
% 15.49/2.55  Current options:
% 15.49/2.55  ------ 
% 15.49/2.55  
% 15.49/2.55  ------ Input Options
% 15.49/2.55  
% 15.49/2.55  --out_options                           all
% 15.49/2.55  --tptp_safe_out                         true
% 15.49/2.55  --problem_path                          ""
% 15.49/2.55  --include_path                          ""
% 15.49/2.55  --clausifier                            res/vclausify_rel
% 15.49/2.55  --clausifier_options                    --mode clausify
% 15.49/2.55  --stdin                                 false
% 15.49/2.55  --stats_out                             all
% 15.49/2.55  
% 15.49/2.55  ------ General Options
% 15.49/2.55  
% 15.49/2.55  --fof                                   false
% 15.49/2.55  --time_out_real                         305.
% 15.49/2.55  --time_out_virtual                      -1.
% 15.49/2.55  --symbol_type_check                     false
% 15.49/2.55  --clausify_out                          false
% 15.49/2.55  --sig_cnt_out                           false
% 15.49/2.55  --trig_cnt_out                          false
% 15.49/2.55  --trig_cnt_out_tolerance                1.
% 15.49/2.55  --trig_cnt_out_sk_spl                   false
% 15.49/2.55  --abstr_cl_out                          false
% 15.49/2.55  
% 15.49/2.55  ------ Global Options
% 15.49/2.55  
% 15.49/2.55  --schedule                              default
% 15.49/2.55  --add_important_lit                     false
% 15.49/2.55  --prop_solver_per_cl                    1000
% 15.49/2.55  --min_unsat_core                        false
% 15.49/2.55  --soft_assumptions                      false
% 15.49/2.55  --soft_lemma_size                       3
% 15.49/2.55  --prop_impl_unit_size                   0
% 15.49/2.55  --prop_impl_unit                        []
% 15.49/2.55  --share_sel_clauses                     true
% 15.49/2.55  --reset_solvers                         false
% 15.49/2.55  --bc_imp_inh                            [conj_cone]
% 15.49/2.55  --conj_cone_tolerance                   3.
% 15.49/2.55  --extra_neg_conj                        none
% 15.49/2.55  --large_theory_mode                     true
% 15.49/2.55  --prolific_symb_bound                   200
% 15.49/2.55  --lt_threshold                          2000
% 15.49/2.55  --clause_weak_htbl                      true
% 15.49/2.55  --gc_record_bc_elim                     false
% 15.49/2.55  
% 15.49/2.55  ------ Preprocessing Options
% 15.49/2.55  
% 15.49/2.55  --preprocessing_flag                    true
% 15.49/2.55  --time_out_prep_mult                    0.1
% 15.49/2.55  --splitting_mode                        input
% 15.49/2.55  --splitting_grd                         true
% 15.49/2.55  --splitting_cvd                         false
% 15.49/2.55  --splitting_cvd_svl                     false
% 15.49/2.55  --splitting_nvd                         32
% 15.49/2.55  --sub_typing                            true
% 15.49/2.55  --prep_gs_sim                           true
% 15.49/2.55  --prep_unflatten                        true
% 15.49/2.55  --prep_res_sim                          true
% 15.49/2.55  --prep_upred                            true
% 15.49/2.55  --prep_sem_filter                       exhaustive
% 15.49/2.55  --prep_sem_filter_out                   false
% 15.49/2.55  --pred_elim                             true
% 15.49/2.55  --res_sim_input                         true
% 15.49/2.55  --eq_ax_congr_red                       true
% 15.49/2.55  --pure_diseq_elim                       true
% 15.49/2.55  --brand_transform                       false
% 15.49/2.55  --non_eq_to_eq                          false
% 15.49/2.55  --prep_def_merge                        true
% 15.49/2.55  --prep_def_merge_prop_impl              false
% 15.49/2.55  --prep_def_merge_mbd                    true
% 15.49/2.55  --prep_def_merge_tr_red                 false
% 15.49/2.55  --prep_def_merge_tr_cl                  false
% 15.49/2.55  --smt_preprocessing                     true
% 15.49/2.55  --smt_ac_axioms                         fast
% 15.49/2.55  --preprocessed_out                      false
% 15.49/2.55  --preprocessed_stats                    false
% 15.49/2.55  
% 15.49/2.55  ------ Abstraction refinement Options
% 15.49/2.55  
% 15.49/2.55  --abstr_ref                             []
% 15.49/2.55  --abstr_ref_prep                        false
% 15.49/2.55  --abstr_ref_until_sat                   false
% 15.49/2.55  --abstr_ref_sig_restrict                funpre
% 15.49/2.55  --abstr_ref_af_restrict_to_split_sk     false
% 15.49/2.55  --abstr_ref_under                       []
% 15.49/2.55  
% 15.49/2.55  ------ SAT Options
% 15.49/2.55  
% 15.49/2.55  --sat_mode                              false
% 15.49/2.55  --sat_fm_restart_options                ""
% 15.49/2.55  --sat_gr_def                            false
% 15.49/2.55  --sat_epr_types                         true
% 15.49/2.55  --sat_non_cyclic_types                  false
% 15.49/2.55  --sat_finite_models                     false
% 15.49/2.55  --sat_fm_lemmas                         false
% 15.49/2.55  --sat_fm_prep                           false
% 15.49/2.55  --sat_fm_uc_incr                        true
% 15.49/2.55  --sat_out_model                         small
% 15.49/2.55  --sat_out_clauses                       false
% 15.49/2.55  
% 15.49/2.55  ------ QBF Options
% 15.49/2.55  
% 15.49/2.55  --qbf_mode                              false
% 15.49/2.55  --qbf_elim_univ                         false
% 15.49/2.55  --qbf_dom_inst                          none
% 15.49/2.55  --qbf_dom_pre_inst                      false
% 15.49/2.55  --qbf_sk_in                             false
% 15.49/2.55  --qbf_pred_elim                         true
% 15.49/2.55  --qbf_split                             512
% 15.49/2.55  
% 15.49/2.55  ------ BMC1 Options
% 15.49/2.55  
% 15.49/2.55  --bmc1_incremental                      false
% 15.49/2.55  --bmc1_axioms                           reachable_all
% 15.49/2.55  --bmc1_min_bound                        0
% 15.49/2.55  --bmc1_max_bound                        -1
% 15.49/2.55  --bmc1_max_bound_default                -1
% 15.49/2.55  --bmc1_symbol_reachability              true
% 15.49/2.55  --bmc1_property_lemmas                  false
% 15.49/2.55  --bmc1_k_induction                      false
% 15.49/2.55  --bmc1_non_equiv_states                 false
% 15.49/2.55  --bmc1_deadlock                         false
% 15.49/2.55  --bmc1_ucm                              false
% 15.49/2.55  --bmc1_add_unsat_core                   none
% 15.49/2.55  --bmc1_unsat_core_children              false
% 15.49/2.55  --bmc1_unsat_core_extrapolate_axioms    false
% 15.49/2.55  --bmc1_out_stat                         full
% 15.49/2.55  --bmc1_ground_init                      false
% 15.49/2.55  --bmc1_pre_inst_next_state              false
% 15.49/2.55  --bmc1_pre_inst_state                   false
% 15.49/2.55  --bmc1_pre_inst_reach_state             false
% 15.49/2.55  --bmc1_out_unsat_core                   false
% 15.49/2.55  --bmc1_aig_witness_out                  false
% 15.49/2.55  --bmc1_verbose                          false
% 15.49/2.55  --bmc1_dump_clauses_tptp                false
% 15.49/2.55  --bmc1_dump_unsat_core_tptp             false
% 15.49/2.55  --bmc1_dump_file                        -
% 15.49/2.55  --bmc1_ucm_expand_uc_limit              128
% 15.49/2.55  --bmc1_ucm_n_expand_iterations          6
% 15.49/2.55  --bmc1_ucm_extend_mode                  1
% 15.49/2.55  --bmc1_ucm_init_mode                    2
% 15.49/2.55  --bmc1_ucm_cone_mode                    none
% 15.49/2.55  --bmc1_ucm_reduced_relation_type        0
% 15.49/2.55  --bmc1_ucm_relax_model                  4
% 15.49/2.55  --bmc1_ucm_full_tr_after_sat            true
% 15.49/2.55  --bmc1_ucm_expand_neg_assumptions       false
% 15.49/2.55  --bmc1_ucm_layered_model                none
% 15.49/2.55  --bmc1_ucm_max_lemma_size               10
% 15.49/2.55  
% 15.49/2.55  ------ AIG Options
% 15.49/2.55  
% 15.49/2.55  --aig_mode                              false
% 15.49/2.55  
% 15.49/2.55  ------ Instantiation Options
% 15.49/2.55  
% 15.49/2.55  --instantiation_flag                    true
% 15.49/2.55  --inst_sos_flag                         false
% 15.49/2.55  --inst_sos_phase                        true
% 15.49/2.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.49/2.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.49/2.55  --inst_lit_sel_side                     none
% 15.49/2.55  --inst_solver_per_active                1400
% 15.49/2.55  --inst_solver_calls_frac                1.
% 15.49/2.55  --inst_passive_queue_type               priority_queues
% 15.49/2.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.49/2.55  --inst_passive_queues_freq              [25;2]
% 15.49/2.55  --inst_dismatching                      true
% 15.49/2.55  --inst_eager_unprocessed_to_passive     true
% 15.49/2.55  --inst_prop_sim_given                   true
% 15.49/2.55  --inst_prop_sim_new                     false
% 15.49/2.55  --inst_subs_new                         false
% 15.49/2.55  --inst_eq_res_simp                      false
% 15.49/2.55  --inst_subs_given                       false
% 15.49/2.55  --inst_orphan_elimination               true
% 15.49/2.55  --inst_learning_loop_flag               true
% 15.49/2.55  --inst_learning_start                   3000
% 15.49/2.55  --inst_learning_factor                  2
% 15.49/2.55  --inst_start_prop_sim_after_learn       3
% 15.49/2.55  --inst_sel_renew                        solver
% 15.49/2.55  --inst_lit_activity_flag                true
% 15.49/2.55  --inst_restr_to_given                   false
% 15.49/2.55  --inst_activity_threshold               500
% 15.49/2.55  --inst_out_proof                        true
% 15.49/2.55  
% 15.49/2.55  ------ Resolution Options
% 15.49/2.55  
% 15.49/2.55  --resolution_flag                       false
% 15.49/2.55  --res_lit_sel                           adaptive
% 15.49/2.55  --res_lit_sel_side                      none
% 15.49/2.55  --res_ordering                          kbo
% 15.49/2.55  --res_to_prop_solver                    active
% 15.49/2.55  --res_prop_simpl_new                    false
% 15.49/2.55  --res_prop_simpl_given                  true
% 15.49/2.55  --res_passive_queue_type                priority_queues
% 15.49/2.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.49/2.55  --res_passive_queues_freq               [15;5]
% 15.49/2.55  --res_forward_subs                      full
% 15.49/2.55  --res_backward_subs                     full
% 15.49/2.55  --res_forward_subs_resolution           true
% 15.49/2.55  --res_backward_subs_resolution          true
% 15.49/2.55  --res_orphan_elimination                true
% 15.49/2.55  --res_time_limit                        2.
% 15.49/2.55  --res_out_proof                         true
% 15.49/2.55  
% 15.49/2.55  ------ Superposition Options
% 15.49/2.55  
% 15.49/2.55  --superposition_flag                    true
% 15.49/2.55  --sup_passive_queue_type                priority_queues
% 15.49/2.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.49/2.55  --sup_passive_queues_freq               [8;1;4]
% 15.49/2.55  --demod_completeness_check              fast
% 15.49/2.55  --demod_use_ground                      true
% 15.49/2.55  --sup_to_prop_solver                    passive
% 15.49/2.55  --sup_prop_simpl_new                    true
% 15.49/2.55  --sup_prop_simpl_given                  true
% 15.49/2.55  --sup_fun_splitting                     false
% 15.49/2.55  --sup_smt_interval                      50000
% 15.49/2.55  
% 15.49/2.55  ------ Superposition Simplification Setup
% 15.49/2.55  
% 15.49/2.55  --sup_indices_passive                   []
% 15.49/2.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.55  --sup_full_triv                         [TrivRules;PropSubs]
% 15.49/2.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.49/2.55  --sup_full_bw                           [BwDemod]
% 15.49/2.55  --sup_immed_triv                        [TrivRules]
% 15.49/2.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.49/2.55  --sup_immed_bw_main                     []
% 15.49/2.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.49/2.55  --sup_input_triv                        [Unflattening;TrivRules]
% 15.49/2.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.49/2.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.49/2.55  
% 15.49/2.55  ------ Combination Options
% 15.49/2.55  
% 15.49/2.55  --comb_res_mult                         3
% 15.49/2.55  --comb_sup_mult                         2
% 15.49/2.55  --comb_inst_mult                        10
% 15.49/2.55  
% 15.49/2.55  ------ Debug Options
% 15.49/2.55  
% 15.49/2.55  --dbg_backtrace                         false
% 15.49/2.55  --dbg_dump_prop_clauses                 false
% 15.49/2.55  --dbg_dump_prop_clauses_file            -
% 15.49/2.55  --dbg_out_stat                          false
% 15.49/2.55  
% 15.49/2.55  
% 15.49/2.55  
% 15.49/2.55  
% 15.49/2.55  ------ Proving...
% 15.49/2.55  
% 15.49/2.55  
% 15.49/2.55  % SZS status Theorem for theBenchmark.p
% 15.49/2.55  
% 15.49/2.55   Resolution empty clause
% 15.49/2.55  
% 15.49/2.55  % SZS output start CNFRefutation for theBenchmark.p
% 15.49/2.55  
% 15.49/2.55  fof(f7,axiom,(
% 15.49/2.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f22,plain,(
% 15.49/2.55    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 15.49/2.55    inference(ennf_transformation,[],[f7])).
% 15.49/2.55  
% 15.49/2.55  fof(f51,plain,(
% 15.49/2.55    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f22])).
% 15.49/2.55  
% 15.49/2.55  fof(f14,conjecture,(
% 15.49/2.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f15,negated_conjecture,(
% 15.49/2.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 15.49/2.55    inference(negated_conjecture,[],[f14])).
% 15.49/2.55  
% 15.49/2.55  fof(f33,plain,(
% 15.49/2.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.49/2.55    inference(ennf_transformation,[],[f15])).
% 15.49/2.55  
% 15.49/2.55  fof(f34,plain,(
% 15.49/2.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.49/2.55    inference(flattening,[],[f33])).
% 15.49/2.55  
% 15.49/2.55  fof(f41,plain,(
% 15.49/2.55    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 15.49/2.55    introduced(choice_axiom,[])).
% 15.49/2.55  
% 15.49/2.55  fof(f40,plain,(
% 15.49/2.55    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 15.49/2.55    introduced(choice_axiom,[])).
% 15.49/2.55  
% 15.49/2.55  fof(f39,plain,(
% 15.49/2.55    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 15.49/2.55    introduced(choice_axiom,[])).
% 15.49/2.55  
% 15.49/2.55  fof(f38,plain,(
% 15.49/2.55    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 15.49/2.55    introduced(choice_axiom,[])).
% 15.49/2.55  
% 15.49/2.55  fof(f37,plain,(
% 15.49/2.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 15.49/2.55    introduced(choice_axiom,[])).
% 15.49/2.55  
% 15.49/2.55  fof(f42,plain,(
% 15.49/2.55    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 15.49/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f41,f40,f39,f38,f37])).
% 15.49/2.55  
% 15.49/2.55  fof(f68,plain,(
% 15.49/2.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f2,axiom,(
% 15.49/2.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f35,plain,(
% 15.49/2.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.49/2.55    inference(nnf_transformation,[],[f2])).
% 15.49/2.55  
% 15.49/2.55  fof(f44,plain,(
% 15.49/2.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.49/2.55    inference(cnf_transformation,[],[f35])).
% 15.49/2.55  
% 15.49/2.55  fof(f1,axiom,(
% 15.49/2.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f17,plain,(
% 15.49/2.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 15.49/2.55    inference(ennf_transformation,[],[f1])).
% 15.49/2.55  
% 15.49/2.55  fof(f18,plain,(
% 15.49/2.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 15.49/2.55    inference(flattening,[],[f17])).
% 15.49/2.55  
% 15.49/2.55  fof(f43,plain,(
% 15.49/2.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f18])).
% 15.49/2.55  
% 15.49/2.55  fof(f45,plain,(
% 15.49/2.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f35])).
% 15.49/2.55  
% 15.49/2.55  fof(f8,axiom,(
% 15.49/2.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f16,plain,(
% 15.49/2.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 15.49/2.55    inference(pure_predicate_removal,[],[f8])).
% 15.49/2.55  
% 15.49/2.55  fof(f23,plain,(
% 15.49/2.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.55    inference(ennf_transformation,[],[f16])).
% 15.49/2.55  
% 15.49/2.55  fof(f52,plain,(
% 15.49/2.55    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.55    inference(cnf_transformation,[],[f23])).
% 15.49/2.55  
% 15.49/2.55  fof(f4,axiom,(
% 15.49/2.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f20,plain,(
% 15.49/2.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.49/2.55    inference(ennf_transformation,[],[f4])).
% 15.49/2.55  
% 15.49/2.55  fof(f36,plain,(
% 15.49/2.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.49/2.55    inference(nnf_transformation,[],[f20])).
% 15.49/2.55  
% 15.49/2.55  fof(f47,plain,(
% 15.49/2.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f36])).
% 15.49/2.55  
% 15.49/2.55  fof(f5,axiom,(
% 15.49/2.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f49,plain,(
% 15.49/2.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.49/2.55    inference(cnf_transformation,[],[f5])).
% 15.49/2.55  
% 15.49/2.55  fof(f3,axiom,(
% 15.49/2.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f19,plain,(
% 15.49/2.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.49/2.55    inference(ennf_transformation,[],[f3])).
% 15.49/2.55  
% 15.49/2.55  fof(f46,plain,(
% 15.49/2.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f19])).
% 15.49/2.55  
% 15.49/2.55  fof(f6,axiom,(
% 15.49/2.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f21,plain,(
% 15.49/2.55    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 15.49/2.55    inference(ennf_transformation,[],[f6])).
% 15.49/2.55  
% 15.49/2.55  fof(f50,plain,(
% 15.49/2.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f21])).
% 15.49/2.55  
% 15.49/2.55  fof(f10,axiom,(
% 15.49/2.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f25,plain,(
% 15.49/2.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 15.49/2.55    inference(ennf_transformation,[],[f10])).
% 15.49/2.55  
% 15.49/2.55  fof(f26,plain,(
% 15.49/2.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 15.49/2.55    inference(flattening,[],[f25])).
% 15.49/2.55  
% 15.49/2.55  fof(f54,plain,(
% 15.49/2.55    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f26])).
% 15.49/2.55  
% 15.49/2.55  fof(f9,axiom,(
% 15.49/2.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f24,plain,(
% 15.49/2.55    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.55    inference(ennf_transformation,[],[f9])).
% 15.49/2.55  
% 15.49/2.55  fof(f53,plain,(
% 15.49/2.55    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.55    inference(cnf_transformation,[],[f24])).
% 15.49/2.55  
% 15.49/2.55  fof(f11,axiom,(
% 15.49/2.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f27,plain,(
% 15.49/2.55    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.49/2.55    inference(ennf_transformation,[],[f11])).
% 15.49/2.55  
% 15.49/2.55  fof(f28,plain,(
% 15.49/2.55    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.49/2.55    inference(flattening,[],[f27])).
% 15.49/2.55  
% 15.49/2.55  fof(f55,plain,(
% 15.49/2.55    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f28])).
% 15.49/2.55  
% 15.49/2.55  fof(f66,plain,(
% 15.49/2.55    v1_funct_1(sK3)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f67,plain,(
% 15.49/2.55    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f13,axiom,(
% 15.49/2.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f31,plain,(
% 15.49/2.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.49/2.55    inference(ennf_transformation,[],[f13])).
% 15.49/2.55  
% 15.49/2.55  fof(f32,plain,(
% 15.49/2.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.49/2.55    inference(flattening,[],[f31])).
% 15.49/2.55  
% 15.49/2.55  fof(f57,plain,(
% 15.49/2.55    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f32])).
% 15.49/2.55  
% 15.49/2.55  fof(f65,plain,(
% 15.49/2.55    m1_pre_topc(sK2,sK0)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f58,plain,(
% 15.49/2.55    ~v2_struct_0(sK0)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f59,plain,(
% 15.49/2.55    v2_pre_topc(sK0)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f60,plain,(
% 15.49/2.55    l1_pre_topc(sK0)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f63,plain,(
% 15.49/2.55    l1_pre_topc(sK1)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f61,plain,(
% 15.49/2.55    ~v2_struct_0(sK1)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f62,plain,(
% 15.49/2.55    v2_pre_topc(sK1)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f71,plain,(
% 15.49/2.55    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f70,plain,(
% 15.49/2.55    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 15.49/2.55    inference(cnf_transformation,[],[f42])).
% 15.49/2.55  
% 15.49/2.55  fof(f12,axiom,(
% 15.49/2.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 15.49/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.49/2.55  
% 15.49/2.55  fof(f29,plain,(
% 15.49/2.55    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.49/2.55    inference(ennf_transformation,[],[f12])).
% 15.49/2.55  
% 15.49/2.55  fof(f30,plain,(
% 15.49/2.55    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.49/2.55    inference(flattening,[],[f29])).
% 15.49/2.55  
% 15.49/2.55  fof(f56,plain,(
% 15.49/2.55    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.55    inference(cnf_transformation,[],[f30])).
% 15.49/2.55  
% 15.49/2.55  cnf(c_8,plain,
% 15.49/2.55      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f51]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1332,plain,
% 15.49/2.55      ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) | ~ v1_relat_1(X0_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_8]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1790,plain,
% 15.49/2.55      ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) = iProver_top
% 15.49/2.55      | v1_relat_1(X0_53) != iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1332]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_18,negated_conjecture,
% 15.49/2.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 15.49/2.55      inference(cnf_transformation,[],[f68]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1326,negated_conjecture,
% 15.49/2.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_18]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1795,plain,
% 15.49/2.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.49/2.55      inference(cnf_transformation,[],[f44]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1335,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) | r1_tarski(X0_53,X1_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_2]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1787,plain,
% 15.49/2.55      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 15.49/2.55      | r1_tarski(X0_53,X1_53) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1335]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2214,plain,
% 15.49/2.55      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_1795,c_1787]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_0,plain,
% 15.49/2.55      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 15.49/2.55      inference(cnf_transformation,[],[f43]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1337,plain,
% 15.49/2.55      ( ~ r1_tarski(X0_53,X1_53)
% 15.49/2.55      | ~ r1_tarski(X2_53,X0_53)
% 15.49/2.55      | r1_tarski(X2_53,X1_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_0]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1785,plain,
% 15.49/2.55      ( r1_tarski(X0_53,X1_53) != iProver_top
% 15.49/2.55      | r1_tarski(X2_53,X0_53) != iProver_top
% 15.49/2.55      | r1_tarski(X2_53,X1_53) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1337]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2360,plain,
% 15.49/2.55      ( r1_tarski(X0_53,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top
% 15.49/2.55      | r1_tarski(X0_53,sK3) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_2214,c_1785]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1,plain,
% 15.49/2.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.49/2.55      inference(cnf_transformation,[],[f45]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1336,plain,
% 15.49/2.55      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) | ~ r1_tarski(X0_53,X1_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_1]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1786,plain,
% 15.49/2.55      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) = iProver_top
% 15.49/2.55      | r1_tarski(X0_53,X1_53) != iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1336]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_9,plain,
% 15.49/2.55      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 15.49/2.55      inference(cnf_transformation,[],[f52]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_5,plain,
% 15.49/2.55      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f47]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_362,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.55      | r1_tarski(k2_relat_1(X0),X2)
% 15.49/2.55      | ~ v1_relat_1(X0) ),
% 15.49/2.55      inference(resolution,[status(thm)],[c_9,c_5]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1324,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 15.49/2.55      | r1_tarski(k2_relat_1(X0_53),X2_53)
% 15.49/2.55      | ~ v1_relat_1(X0_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_362]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1797,plain,
% 15.49/2.55      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 15.49/2.55      | r1_tarski(k2_relat_1(X0_53),X2_53) = iProver_top
% 15.49/2.55      | v1_relat_1(X0_53) != iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_4248,plain,
% 15.49/2.55      ( r1_tarski(X0_53,k2_zfmisc_1(X1_53,X2_53)) != iProver_top
% 15.49/2.55      | r1_tarski(k2_relat_1(X0_53),X2_53) = iProver_top
% 15.49/2.55      | v1_relat_1(X0_53) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_1786,c_1797]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_7141,plain,
% 15.49/2.55      ( r1_tarski(X0_53,sK3) != iProver_top
% 15.49/2.55      | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
% 15.49/2.55      | v1_relat_1(X0_53) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_2360,c_4248]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_6,plain,
% 15.49/2.55      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.49/2.55      inference(cnf_transformation,[],[f49]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1334,plain,
% 15.49/2.55      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_6]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2298,plain,
% 15.49/2.55      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 15.49/2.55      inference(instantiation,[status(thm)],[c_1334]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2299,plain,
% 15.49/2.55      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_2298]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_3,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f46]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_203,plain,
% 15.49/2.55      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.49/2.55      inference(prop_impl,[status(thm)],[c_1]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_204,plain,
% 15.49/2.55      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.49/2.55      inference(renaming,[status(thm)],[c_203]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_257,plain,
% 15.49/2.55      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.49/2.55      inference(bin_hyper_res,[status(thm)],[c_3,c_204]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1325,plain,
% 15.49/2.55      ( ~ r1_tarski(X0_53,X1_53) | ~ v1_relat_1(X1_53) | v1_relat_1(X0_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_257]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1796,plain,
% 15.49/2.55      ( r1_tarski(X0_53,X1_53) != iProver_top
% 15.49/2.55      | v1_relat_1(X1_53) != iProver_top
% 15.49/2.55      | v1_relat_1(X0_53) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1325]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_3316,plain,
% 15.49/2.55      ( r1_tarski(X0_53,sK3) != iProver_top
% 15.49/2.55      | v1_relat_1(X0_53) = iProver_top
% 15.49/2.55      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_2360,c_1796]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_7343,plain,
% 15.49/2.55      ( r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
% 15.49/2.55      | r1_tarski(X0_53,sK3) != iProver_top ),
% 15.49/2.55      inference(global_propositional_subsumption,
% 15.49/2.55                [status(thm)],
% 15.49/2.55                [c_7141,c_2299,c_3316]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_7344,plain,
% 15.49/2.55      ( r1_tarski(X0_53,sK3) != iProver_top
% 15.49/2.55      | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top ),
% 15.49/2.55      inference(renaming,[status(thm)],[c_7343]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_7,plain,
% 15.49/2.55      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f50]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1333,plain,
% 15.49/2.55      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
% 15.49/2.55      | ~ v1_relat_1(X0_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_7]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1789,plain,
% 15.49/2.55      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
% 15.49/2.55      | v1_relat_1(X0_53) != iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_11,plain,
% 15.49/2.55      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.55      | ~ r1_tarski(k1_relat_1(X0),X1)
% 15.49/2.55      | ~ r1_tarski(k2_relat_1(X0),X2)
% 15.49/2.55      | ~ v1_relat_1(X0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f54]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1330,plain,
% 15.49/2.55      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 15.49/2.55      | ~ r1_tarski(k1_relat_1(X0_53),X1_53)
% 15.49/2.55      | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
% 15.49/2.55      | ~ v1_relat_1(X0_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_11]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1792,plain,
% 15.49/2.55      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
% 15.49/2.55      | r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
% 15.49/2.55      | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
% 15.49/2.55      | v1_relat_1(X0_53) != iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_10,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.55      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 15.49/2.55      inference(cnf_transformation,[],[f53]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1331,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 15.49/2.55      | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_10]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1791,plain,
% 15.49/2.55      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 15.49/2.55      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1331]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2712,plain,
% 15.49/2.55      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 15.49/2.55      | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
% 15.49/2.55      | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
% 15.49/2.55      | v1_relat_1(X2_53) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_1792,c_1791]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_7999,plain,
% 15.49/2.55      ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 15.49/2.55      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 15.49/2.55      | v1_relat_1(X2_53) != iProver_top
% 15.49/2.55      | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_1789,c_2712]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_3313,plain,
% 15.49/2.55      ( v1_relat_1(X0_53) != iProver_top
% 15.49/2.55      | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_1790,c_1796]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_50556,plain,
% 15.49/2.55      ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 15.49/2.55      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 15.49/2.55      | v1_relat_1(X2_53) != iProver_top ),
% 15.49/2.55      inference(forward_subsumption_resolution,[status(thm)],[c_7999,c_3313]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_50570,plain,
% 15.49/2.55      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(X1_53,X0_53),X2_53) = k10_relat_1(k7_relat_1(X1_53,X0_53),X2_53)
% 15.49/2.55      | r1_tarski(k7_relat_1(X1_53,X0_53),sK3) != iProver_top
% 15.49/2.55      | v1_relat_1(X1_53) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_7344,c_50556]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_51795,plain,
% 15.49/2.55      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
% 15.49/2.55      | v1_relat_1(sK3) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_1790,c_50570]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_39,plain,
% 15.49/2.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1936,plain,
% 15.49/2.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 15.49/2.55      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 15.49/2.55      inference(instantiation,[status(thm)],[c_1335]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1937,plain,
% 15.49/2.55      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 15.49/2.55      | r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1918,plain,
% 15.49/2.55      ( ~ r1_tarski(X0_53,k2_zfmisc_1(X1_53,X2_53))
% 15.49/2.55      | v1_relat_1(X0_53)
% 15.49/2.55      | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
% 15.49/2.55      inference(instantiation,[status(thm)],[c_1325]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2245,plain,
% 15.49/2.55      ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 15.49/2.55      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 15.49/2.55      | v1_relat_1(sK3) ),
% 15.49/2.55      inference(instantiation,[status(thm)],[c_1918]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2246,plain,
% 15.49/2.55      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 15.49/2.55      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 15.49/2.55      | v1_relat_1(sK3) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_2245]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_53500,plain,
% 15.49/2.55      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
% 15.49/2.55      inference(global_propositional_subsumption,
% 15.49/2.55                [status(thm)],
% 15.49/2.55                [c_51795,c_39,c_1937,c_2246,c_2299]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2693,plain,
% 15.49/2.55      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_1795,c_1791]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_12,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.55      | ~ v1_funct_1(X0)
% 15.49/2.55      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 15.49/2.55      inference(cnf_transformation,[],[f55]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_20,negated_conjecture,
% 15.49/2.55      ( v1_funct_1(sK3) ),
% 15.49/2.55      inference(cnf_transformation,[],[f66]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_474,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.55      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 15.49/2.55      | sK3 != X0 ),
% 15.49/2.55      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_475,plain,
% 15.49/2.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.49/2.55      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 15.49/2.55      inference(unflattening,[status(thm)],[c_474]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1322,plain,
% 15.49/2.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 15.49/2.55      | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_475]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1799,plain,
% 15.49/2.55      ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
% 15.49/2.55      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1994,plain,
% 15.49/2.55      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_1795,c_1799]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_19,negated_conjecture,
% 15.49/2.55      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 15.49/2.55      inference(cnf_transformation,[],[f67]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_14,plain,
% 15.49/2.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.49/2.55      | ~ m1_pre_topc(X3,X1)
% 15.49/2.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.49/2.55      | v2_struct_0(X1)
% 15.49/2.55      | v2_struct_0(X2)
% 15.49/2.55      | ~ v2_pre_topc(X2)
% 15.49/2.55      | ~ v2_pre_topc(X1)
% 15.49/2.55      | ~ l1_pre_topc(X2)
% 15.49/2.55      | ~ l1_pre_topc(X1)
% 15.49/2.55      | ~ v1_funct_1(X0)
% 15.49/2.55      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 15.49/2.55      inference(cnf_transformation,[],[f57]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_21,negated_conjecture,
% 15.49/2.55      ( m1_pre_topc(sK2,sK0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f65]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_381,plain,
% 15.49/2.55      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.49/2.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.49/2.55      | v2_struct_0(X2)
% 15.49/2.55      | v2_struct_0(X1)
% 15.49/2.55      | ~ v2_pre_topc(X2)
% 15.49/2.55      | ~ v2_pre_topc(X1)
% 15.49/2.55      | ~ l1_pre_topc(X2)
% 15.49/2.55      | ~ l1_pre_topc(X1)
% 15.49/2.55      | ~ v1_funct_1(X0)
% 15.49/2.55      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 15.49/2.55      | sK2 != X3
% 15.49/2.55      | sK0 != X1 ),
% 15.49/2.55      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_382,plain,
% 15.49/2.55      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 15.49/2.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 15.49/2.55      | v2_struct_0(X1)
% 15.49/2.55      | v2_struct_0(sK0)
% 15.49/2.55      | ~ v2_pre_topc(X1)
% 15.49/2.55      | ~ v2_pre_topc(sK0)
% 15.49/2.55      | ~ l1_pre_topc(X1)
% 15.49/2.55      | ~ l1_pre_topc(sK0)
% 15.49/2.55      | ~ v1_funct_1(X0)
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 15.49/2.55      inference(unflattening,[status(thm)],[c_381]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_28,negated_conjecture,
% 15.49/2.55      ( ~ v2_struct_0(sK0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f58]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_27,negated_conjecture,
% 15.49/2.55      ( v2_pre_topc(sK0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f59]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_26,negated_conjecture,
% 15.49/2.55      ( l1_pre_topc(sK0) ),
% 15.49/2.55      inference(cnf_transformation,[],[f60]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_386,plain,
% 15.49/2.55      ( ~ l1_pre_topc(X1)
% 15.49/2.55      | v2_struct_0(X1)
% 15.49/2.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 15.49/2.55      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 15.49/2.55      | ~ v2_pre_topc(X1)
% 15.49/2.55      | ~ v1_funct_1(X0)
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 15.49/2.55      inference(global_propositional_subsumption,
% 15.49/2.55                [status(thm)],
% 15.49/2.55                [c_382,c_28,c_27,c_26]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_387,plain,
% 15.49/2.55      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 15.49/2.55      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 15.49/2.55      | v2_struct_0(X1)
% 15.49/2.55      | ~ v2_pre_topc(X1)
% 15.49/2.55      | ~ l1_pre_topc(X1)
% 15.49/2.55      | ~ v1_funct_1(X0)
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 15.49/2.55      inference(renaming,[status(thm)],[c_386]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_422,plain,
% 15.49/2.55      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 15.49/2.55      | v2_struct_0(X1)
% 15.49/2.55      | ~ v2_pre_topc(X1)
% 15.49/2.55      | ~ l1_pre_topc(X1)
% 15.49/2.55      | ~ v1_funct_1(X0)
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
% 15.49/2.55      | u1_struct_0(X1) != u1_struct_0(sK1)
% 15.49/2.55      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 15.49/2.55      | sK3 != X0 ),
% 15.49/2.55      inference(resolution_lifted,[status(thm)],[c_19,c_387]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_423,plain,
% 15.49/2.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 15.49/2.55      | v2_struct_0(X0)
% 15.49/2.55      | ~ v2_pre_topc(X0)
% 15.49/2.55      | ~ l1_pre_topc(X0)
% 15.49/2.55      | ~ v1_funct_1(sK3)
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 15.49/2.55      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 15.49/2.55      inference(unflattening,[status(thm)],[c_422]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_427,plain,
% 15.49/2.55      ( ~ l1_pre_topc(X0)
% 15.49/2.55      | ~ v2_pre_topc(X0)
% 15.49/2.55      | v2_struct_0(X0)
% 15.49/2.55      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 15.49/2.55      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 15.49/2.55      inference(global_propositional_subsumption,[status(thm)],[c_423,c_20]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_428,plain,
% 15.49/2.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 15.49/2.55      | v2_struct_0(X0)
% 15.49/2.55      | ~ v2_pre_topc(X0)
% 15.49/2.55      | ~ l1_pre_topc(X0)
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 15.49/2.55      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 15.49/2.55      inference(renaming,[status(thm)],[c_427]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_23,negated_conjecture,
% 15.49/2.55      ( l1_pre_topc(sK1) ),
% 15.49/2.55      inference(cnf_transformation,[],[f63]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_493,plain,
% 15.49/2.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 15.49/2.55      | v2_struct_0(X0)
% 15.49/2.55      | ~ v2_pre_topc(X0)
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 15.49/2.55      | u1_struct_0(X0) != u1_struct_0(sK1)
% 15.49/2.55      | sK1 != X0 ),
% 15.49/2.55      inference(resolution_lifted,[status(thm)],[c_428,c_23]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_494,plain,
% 15.49/2.55      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 15.49/2.55      | v2_struct_0(sK1)
% 15.49/2.55      | ~ v2_pre_topc(sK1)
% 15.49/2.55      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 15.49/2.55      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 15.49/2.55      inference(unflattening,[status(thm)],[c_493]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_25,negated_conjecture,
% 15.49/2.55      ( ~ v2_struct_0(sK1) ),
% 15.49/2.55      inference(cnf_transformation,[],[f61]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_24,negated_conjecture,
% 15.49/2.55      ( v2_pre_topc(sK1) ),
% 15.49/2.55      inference(cnf_transformation,[],[f62]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_496,plain,
% 15.49/2.55      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 15.49/2.55      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 15.49/2.55      inference(global_propositional_subsumption,
% 15.49/2.55                [status(thm)],
% 15.49/2.55                [c_494,c_25,c_24,c_18]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_877,plain,
% 15.49/2.55      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 15.49/2.55      inference(equality_resolution_simp,[status(thm)],[c_496]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1320,plain,
% 15.49/2.55      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_877]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2033,plain,
% 15.49/2.55      ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 15.49/2.55      inference(demodulation,[status(thm)],[c_1994,c_1320]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_15,negated_conjecture,
% 15.49/2.55      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 15.49/2.55      inference(cnf_transformation,[],[f71]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1329,negated_conjecture,
% 15.49/2.55      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_15]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2440,plain,
% 15.49/2.55      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
% 15.49/2.55      inference(demodulation,[status(thm)],[c_2033,c_1329]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2874,plain,
% 15.49/2.55      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 15.49/2.55      inference(demodulation,[status(thm)],[c_2693,c_2440]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_53504,plain,
% 15.49/2.55      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 15.49/2.55      inference(demodulation,[status(thm)],[c_53500,c_2874]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_16,negated_conjecture,
% 15.49/2.55      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 15.49/2.55      inference(cnf_transformation,[],[f70]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1328,negated_conjecture,
% 15.49/2.55      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_16]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1793,plain,
% 15.49/2.55      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2876,plain,
% 15.49/2.55      ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 15.49/2.55      inference(demodulation,[status(thm)],[c_2693,c_1793]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_13,plain,
% 15.49/2.55      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 15.49/2.55      | ~ v1_funct_1(X0)
% 15.49/2.55      | ~ v1_relat_1(X0)
% 15.49/2.55      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
% 15.49/2.55      inference(cnf_transformation,[],[f56]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_459,plain,
% 15.49/2.55      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 15.49/2.55      | ~ v1_relat_1(X0)
% 15.49/2.55      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
% 15.49/2.55      | sK3 != X0 ),
% 15.49/2.55      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_460,plain,
% 15.49/2.55      ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
% 15.49/2.55      | ~ v1_relat_1(sK3)
% 15.49/2.55      | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
% 15.49/2.55      inference(unflattening,[status(thm)],[c_459]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1323,plain,
% 15.49/2.55      ( ~ r1_tarski(k10_relat_1(sK3,X0_53),X1_53)
% 15.49/2.55      | ~ v1_relat_1(sK3)
% 15.49/2.55      | k10_relat_1(k7_relat_1(sK3,X1_53),X0_53) = k10_relat_1(sK3,X0_53) ),
% 15.49/2.55      inference(subtyping,[status(esa)],[c_460]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_1798,plain,
% 15.49/2.55      ( k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(sK3,X1_53)
% 15.49/2.55      | r1_tarski(k10_relat_1(sK3,X1_53),X0_53) != iProver_top
% 15.49/2.55      | v1_relat_1(sK3) != iProver_top ),
% 15.49/2.55      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_2892,plain,
% 15.49/2.55      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4)
% 15.49/2.55      | v1_relat_1(sK3) != iProver_top ),
% 15.49/2.55      inference(superposition,[status(thm)],[c_2876,c_1798]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_3116,plain,
% 15.49/2.55      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
% 15.49/2.55      inference(global_propositional_subsumption,
% 15.49/2.55                [status(thm)],
% 15.49/2.55                [c_2892,c_39,c_1937,c_2246,c_2299]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_53505,plain,
% 15.49/2.55      ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
% 15.49/2.55      inference(light_normalisation,[status(thm)],[c_53504,c_3116]) ).
% 15.49/2.55  
% 15.49/2.55  cnf(c_53506,plain,
% 15.49/2.55      ( $false ),
% 15.49/2.55      inference(equality_resolution_simp,[status(thm)],[c_53505]) ).
% 15.49/2.55  
% 15.49/2.55  
% 15.49/2.55  % SZS output end CNFRefutation for theBenchmark.p
% 15.49/2.55  
% 15.49/2.55  ------                               Statistics
% 15.49/2.55  
% 15.49/2.55  ------ General
% 15.49/2.55  
% 15.49/2.55  abstr_ref_over_cycles:                  0
% 15.49/2.55  abstr_ref_under_cycles:                 0
% 15.49/2.55  gc_basic_clause_elim:                   0
% 15.49/2.55  forced_gc_time:                         0
% 15.49/2.55  parsing_time:                           0.008
% 15.49/2.55  unif_index_cands_time:                  0.
% 15.49/2.55  unif_index_add_time:                    0.
% 15.49/2.55  orderings_time:                         0.
% 15.49/2.55  out_proof_time:                         0.014
% 15.49/2.55  total_time:                             1.703
% 15.49/2.55  num_of_symbols:                         59
% 15.49/2.55  num_of_terms:                           64499
% 15.49/2.55  
% 15.49/2.55  ------ Preprocessing
% 15.49/2.55  
% 15.49/2.55  num_of_splits:                          0
% 15.49/2.55  num_of_split_atoms:                     0
% 15.49/2.55  num_of_reused_defs:                     0
% 15.49/2.55  num_eq_ax_congr_red:                    17
% 15.49/2.55  num_of_sem_filtered_clauses:            1
% 15.49/2.55  num_of_subtypes:                        3
% 15.49/2.55  monotx_restored_types:                  0
% 15.49/2.55  sat_num_of_epr_types:                   0
% 15.49/2.55  sat_num_of_non_cyclic_types:            0
% 15.49/2.55  sat_guarded_non_collapsed_types:        0
% 15.49/2.55  num_pure_diseq_elim:                    0
% 15.49/2.55  simp_replaced_by:                       0
% 15.49/2.55  res_preprocessed:                       112
% 15.49/2.55  prep_upred:                             0
% 15.49/2.55  prep_unflattend:                        33
% 15.49/2.55  smt_new_axioms:                         0
% 15.49/2.55  pred_elim_cands:                        3
% 15.49/2.55  pred_elim:                              7
% 15.49/2.55  pred_elim_cl:                           11
% 15.49/2.55  pred_elim_cycles:                       9
% 15.49/2.55  merged_defs:                            8
% 15.49/2.55  merged_defs_ncl:                        0
% 15.49/2.55  bin_hyper_res:                          9
% 15.49/2.55  prep_cycles:                            4
% 15.49/2.55  pred_elim_time:                         0.01
% 15.49/2.55  splitting_time:                         0.
% 15.49/2.55  sem_filter_time:                        0.
% 15.49/2.55  monotx_time:                            0.
% 15.49/2.55  subtype_inf_time:                       0.
% 15.49/2.55  
% 15.49/2.55  ------ Problem properties
% 15.49/2.55  
% 15.49/2.55  clauses:                                18
% 15.49/2.55  conjectures:                            4
% 15.49/2.55  epr:                                    2
% 15.49/2.55  horn:                                   18
% 15.49/2.55  ground:                                 6
% 15.49/2.55  unary:                                  6
% 15.49/2.55  binary:                                 6
% 15.49/2.55  lits:                                   37
% 15.49/2.55  lits_eq:                                7
% 15.49/2.55  fd_pure:                                0
% 15.49/2.55  fd_pseudo:                              0
% 15.49/2.55  fd_cond:                                0
% 15.49/2.55  fd_pseudo_cond:                         0
% 15.49/2.55  ac_symbols:                             0
% 15.49/2.55  
% 15.49/2.55  ------ Propositional Solver
% 15.49/2.55  
% 15.49/2.55  prop_solver_calls:                      31
% 15.49/2.55  prop_fast_solver_calls:                 1785
% 15.49/2.55  smt_solver_calls:                       0
% 15.49/2.55  smt_fast_solver_calls:                  0
% 15.49/2.55  prop_num_of_clauses:                    19096
% 15.49/2.55  prop_preprocess_simplified:             29023
% 15.49/2.55  prop_fo_subsumed:                       70
% 15.49/2.55  prop_solver_time:                       0.
% 15.49/2.55  smt_solver_time:                        0.
% 15.49/2.55  smt_fast_solver_time:                   0.
% 15.49/2.55  prop_fast_solver_time:                  0.
% 15.49/2.55  prop_unsat_core_time:                   0.
% 15.49/2.55  
% 15.49/2.55  ------ QBF
% 15.49/2.55  
% 15.49/2.55  qbf_q_res:                              0
% 15.49/2.55  qbf_num_tautologies:                    0
% 15.49/2.55  qbf_prep_cycles:                        0
% 15.49/2.55  
% 15.49/2.55  ------ BMC1
% 15.49/2.55  
% 15.49/2.55  bmc1_current_bound:                     -1
% 15.49/2.55  bmc1_last_solved_bound:                 -1
% 15.49/2.55  bmc1_unsat_core_size:                   -1
% 15.49/2.55  bmc1_unsat_core_parents_size:           -1
% 15.49/2.55  bmc1_merge_next_fun:                    0
% 15.49/2.55  bmc1_unsat_core_clauses_time:           0.
% 15.49/2.55  
% 15.49/2.55  ------ Instantiation
% 15.49/2.55  
% 15.49/2.55  inst_num_of_clauses:                    4040
% 15.49/2.55  inst_num_in_passive:                    682
% 15.49/2.55  inst_num_in_active:                     1580
% 15.49/2.55  inst_num_in_unprocessed:                1778
% 15.49/2.55  inst_num_of_loops:                      1650
% 15.49/2.55  inst_num_of_learning_restarts:          0
% 15.49/2.55  inst_num_moves_active_passive:          67
% 15.49/2.55  inst_lit_activity:                      0
% 15.49/2.55  inst_lit_activity_moves:                0
% 15.49/2.55  inst_num_tautologies:                   0
% 15.49/2.55  inst_num_prop_implied:                  0
% 15.49/2.55  inst_num_existing_simplified:           0
% 15.49/2.55  inst_num_eq_res_simplified:             0
% 15.49/2.55  inst_num_child_elim:                    0
% 15.49/2.55  inst_num_of_dismatching_blockings:      5105
% 15.49/2.55  inst_num_of_non_proper_insts:           5196
% 15.49/2.55  inst_num_of_duplicates:                 0
% 15.49/2.55  inst_inst_num_from_inst_to_res:         0
% 15.49/2.55  inst_dismatching_checking_time:         0.
% 15.49/2.55  
% 15.49/2.55  ------ Resolution
% 15.49/2.55  
% 15.49/2.55  res_num_of_clauses:                     0
% 15.49/2.55  res_num_in_passive:                     0
% 15.49/2.55  res_num_in_active:                      0
% 15.49/2.55  res_num_of_loops:                       116
% 15.49/2.55  res_forward_subset_subsumed:            178
% 15.49/2.55  res_backward_subset_subsumed:           0
% 15.49/2.55  res_forward_subsumed:                   0
% 15.49/2.55  res_backward_subsumed:                  0
% 15.49/2.55  res_forward_subsumption_resolution:     0
% 15.49/2.55  res_backward_subsumption_resolution:    0
% 15.49/2.55  res_clause_to_clause_subsumption:       8638
% 15.49/2.55  res_orphan_elimination:                 0
% 15.49/2.55  res_tautology_del:                      888
% 15.49/2.55  res_num_eq_res_simplified:              1
% 15.49/2.55  res_num_sel_changes:                    0
% 15.49/2.55  res_moves_from_active_to_pass:          0
% 15.49/2.55  
% 15.49/2.55  ------ Superposition
% 15.49/2.55  
% 15.49/2.55  sup_time_total:                         0.
% 15.49/2.55  sup_time_generating:                    0.
% 15.49/2.55  sup_time_sim_full:                      0.
% 15.49/2.55  sup_time_sim_immed:                     0.
% 15.49/2.55  
% 15.49/2.55  sup_num_of_clauses:                     1414
% 15.49/2.55  sup_num_in_active:                      322
% 15.49/2.55  sup_num_in_passive:                     1092
% 15.49/2.55  sup_num_of_loops:                       328
% 15.49/2.55  sup_fw_superposition:                   768
% 15.49/2.55  sup_bw_superposition:                   996
% 15.49/2.55  sup_immediate_simplified:               260
% 15.49/2.55  sup_given_eliminated:                   0
% 15.49/2.55  comparisons_done:                       0
% 15.49/2.55  comparisons_avoided:                    0
% 15.49/2.55  
% 15.49/2.55  ------ Simplifications
% 15.49/2.55  
% 15.49/2.55  
% 15.49/2.55  sim_fw_subset_subsumed:                 110
% 15.49/2.55  sim_bw_subset_subsumed:                 33
% 15.49/2.55  sim_fw_subsumed:                        132
% 15.49/2.55  sim_bw_subsumed:                        11
% 15.49/2.55  sim_fw_subsumption_res:                 4
% 15.49/2.55  sim_bw_subsumption_res:                 5
% 15.49/2.55  sim_tautology_del:                      4
% 15.49/2.55  sim_eq_tautology_del:                   0
% 15.49/2.55  sim_eq_res_simp:                        0
% 15.49/2.55  sim_fw_demodulated:                     2
% 15.49/2.55  sim_bw_demodulated:                     6
% 15.49/2.55  sim_light_normalised:                   1
% 15.49/2.55  sim_joinable_taut:                      0
% 15.49/2.55  sim_joinable_simp:                      0
% 15.49/2.55  sim_ac_normalised:                      0
% 15.49/2.55  sim_smt_subsumption:                    0
% 15.49/2.55  
%------------------------------------------------------------------------------
