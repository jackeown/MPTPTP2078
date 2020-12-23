%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:35 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 484 expanded)
%              Number of clauses        :  108 ( 168 expanded)
%              Number of leaves         :   20 ( 153 expanded)
%              Depth                    :   25
%              Number of atoms          :  624 (3905 expanded)
%              Number of equality atoms :  155 ( 489 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4)
        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f36,f43,f42,f41,f40,f39])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1571,plain,
    ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2097,plain,
    ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1571])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1564,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1570,plain,
    ( v5_relat_1(X0_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2098,plain,
    ( v5_relat_1(X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_2860,plain,
    ( v5_relat_1(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2103,c_2098])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1579,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2089,plain,
    ( r1_tarski(X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1579])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1577,plain,
    ( ~ v5_relat_1(X0_53,X1_53)
    | v5_relat_1(X2_53,X1_53)
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(X0_53))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2091,plain,
    ( v5_relat_1(X0_53,X1_53) != iProver_top
    | v5_relat_1(X2_53,X1_53) = iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1577])).

cnf(c_2879,plain,
    ( v5_relat_1(X0_53,X1_53) != iProver_top
    | v5_relat_1(X2_53,X1_53) = iProver_top
    | r1_tarski(X2_53,X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2089,c_2091])).

cnf(c_4213,plain,
    ( v5_relat_1(X0_53,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0_53,sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_2879])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1578,plain,
    ( r1_tarski(X0_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2265,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_2266,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2265])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_267,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_212])).

cnf(c_1563,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_267])).

cnf(c_2247,plain,
    ( ~ r1_tarski(X0_53,k2_zfmisc_1(X1_53,X2_53))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_2575,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2247])).

cnf(c_2576,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2575])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1573,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2613,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_2614,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2613])).

cnf(c_4500,plain,
    ( r1_tarski(X0_53,sK3) != iProver_top
    | v5_relat_1(X0_53,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4213,c_40,c_2266,c_2576,c_2614])).

cnf(c_4501,plain,
    ( v5_relat_1(X0_53,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0_53,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4500])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1575,plain,
    ( ~ v5_relat_1(X0_53,X1_53)
    | r1_tarski(k2_relat_1(X0_53),X1_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2093,plain,
    ( v5_relat_1(X0_53,X1_53) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X1_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1572,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2096,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1572])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1568,plain,
    ( ~ r1_tarski(k1_relat_1(X0_53),X1_53)
    | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2100,plain,
    ( r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1569,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2099,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_3046,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
    | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2099])).

cnf(c_6038,plain,
    ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top
    | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2096,c_3046])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1574,plain,
    ( ~ v1_relat_1(X0_53)
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2094,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(c_7524,plain,
    ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6038,c_2094])).

cnf(c_7528,plain,
    ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | v5_relat_1(k7_relat_1(X2_53,X0_53),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top
    | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2093,c_7524])).

cnf(c_7559,plain,
    ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | v5_relat_1(k7_relat_1(X2_53,X0_53),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7528,c_2094])).

cnf(c_7563,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(X1_53,X0_53),X2_53) = k10_relat_1(k7_relat_1(X1_53,X0_53),X2_53)
    | r1_tarski(k7_relat_1(X1_53,X0_53),sK3) != iProver_top
    | v1_relat_1(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_4501,c_7559])).

cnf(c_7678,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_7563])).

cnf(c_7683,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7678,c_40,c_2266,c_2576,c_2614])).

cnf(c_3025,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_2103,c_2099])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_469,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
    inference(subtyping,[status(esa)],[c_469])).

cnf(c_2106,plain,
    ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_2326,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_2103,c_2106])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_375,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK2 != X3
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_376,plain,
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
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_380,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_29,c_28,c_27])).

cnf(c_381,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_380])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_381])).

cnf(c_417,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_421,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_21])).

cnf(c_422,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_487,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_422,c_24])).

cnf(c_488,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_490,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_26,c_25,c_19])).

cnf(c_987,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_490])).

cnf(c_1559,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_987])).

cnf(c_2358,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_2326,c_1559])).

cnf(c_16,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1567,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2748,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2358,c_1567])).

cnf(c_3205,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3025,c_2748])).

cnf(c_7687,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_7683,c_3205])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1566,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2101,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1566])).

cnf(c_3206,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3025,c_2101])).

cnf(c_14,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_453,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_454,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_1562,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0_53),X1_53)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X1_53),X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_2105,plain,
    ( k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(sK3,X1_53)
    | r1_tarski(k10_relat_1(sK3,X1_53),X0_53) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_3252,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_2105])).

cnf(c_3427,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3252,c_40,c_2266,c_2576,c_2614])).

cnf(c_7688,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_7687,c_3427])).

cnf(c_7689,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7688])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:37:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.30/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/0.98  
% 3.30/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/0.98  
% 3.30/0.98  ------  iProver source info
% 3.30/0.98  
% 3.30/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.30/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/0.98  git: non_committed_changes: false
% 3.30/0.98  git: last_make_outside_of_git: false
% 3.30/0.98  
% 3.30/0.98  ------ 
% 3.30/0.98  
% 3.30/0.98  ------ Input Options
% 3.30/0.98  
% 3.30/0.98  --out_options                           all
% 3.30/0.98  --tptp_safe_out                         true
% 3.30/0.98  --problem_path                          ""
% 3.30/0.98  --include_path                          ""
% 3.30/0.98  --clausifier                            res/vclausify_rel
% 3.30/0.98  --clausifier_options                    --mode clausify
% 3.30/0.98  --stdin                                 false
% 3.30/0.98  --stats_out                             all
% 3.30/0.98  
% 3.30/0.98  ------ General Options
% 3.30/0.98  
% 3.30/0.98  --fof                                   false
% 3.30/0.98  --time_out_real                         305.
% 3.30/0.98  --time_out_virtual                      -1.
% 3.30/0.98  --symbol_type_check                     false
% 3.30/0.98  --clausify_out                          false
% 3.30/0.98  --sig_cnt_out                           false
% 3.30/0.98  --trig_cnt_out                          false
% 3.30/0.98  --trig_cnt_out_tolerance                1.
% 3.30/0.98  --trig_cnt_out_sk_spl                   false
% 3.30/0.98  --abstr_cl_out                          false
% 3.30/0.98  
% 3.30/0.98  ------ Global Options
% 3.30/0.98  
% 3.30/0.98  --schedule                              default
% 3.30/0.98  --add_important_lit                     false
% 3.30/0.98  --prop_solver_per_cl                    1000
% 3.30/0.98  --min_unsat_core                        false
% 3.30/0.98  --soft_assumptions                      false
% 3.30/0.98  --soft_lemma_size                       3
% 3.30/0.98  --prop_impl_unit_size                   0
% 3.30/0.98  --prop_impl_unit                        []
% 3.30/0.98  --share_sel_clauses                     true
% 3.30/0.98  --reset_solvers                         false
% 3.30/0.98  --bc_imp_inh                            [conj_cone]
% 3.30/0.98  --conj_cone_tolerance                   3.
% 3.30/0.98  --extra_neg_conj                        none
% 3.30/0.98  --large_theory_mode                     true
% 3.30/0.98  --prolific_symb_bound                   200
% 3.30/0.98  --lt_threshold                          2000
% 3.30/0.98  --clause_weak_htbl                      true
% 3.30/0.98  --gc_record_bc_elim                     false
% 3.30/0.98  
% 3.30/0.98  ------ Preprocessing Options
% 3.30/0.98  
% 3.30/0.98  --preprocessing_flag                    true
% 3.30/0.98  --time_out_prep_mult                    0.1
% 3.30/0.98  --splitting_mode                        input
% 3.30/0.98  --splitting_grd                         true
% 3.30/0.98  --splitting_cvd                         false
% 3.30/0.98  --splitting_cvd_svl                     false
% 3.30/0.98  --splitting_nvd                         32
% 3.30/0.98  --sub_typing                            true
% 3.30/0.98  --prep_gs_sim                           true
% 3.30/0.98  --prep_unflatten                        true
% 3.30/0.98  --prep_res_sim                          true
% 3.30/0.98  --prep_upred                            true
% 3.30/0.98  --prep_sem_filter                       exhaustive
% 3.30/0.98  --prep_sem_filter_out                   false
% 3.30/0.98  --pred_elim                             true
% 3.30/0.98  --res_sim_input                         true
% 3.30/0.98  --eq_ax_congr_red                       true
% 3.30/0.98  --pure_diseq_elim                       true
% 3.30/0.98  --brand_transform                       false
% 3.30/0.98  --non_eq_to_eq                          false
% 3.30/0.98  --prep_def_merge                        true
% 3.30/0.98  --prep_def_merge_prop_impl              false
% 3.30/0.98  --prep_def_merge_mbd                    true
% 3.30/0.98  --prep_def_merge_tr_red                 false
% 3.30/0.98  --prep_def_merge_tr_cl                  false
% 3.30/0.98  --smt_preprocessing                     true
% 3.30/0.98  --smt_ac_axioms                         fast
% 3.30/0.98  --preprocessed_out                      false
% 3.30/0.98  --preprocessed_stats                    false
% 3.30/0.98  
% 3.30/0.98  ------ Abstraction refinement Options
% 3.30/0.98  
% 3.30/0.98  --abstr_ref                             []
% 3.30/0.98  --abstr_ref_prep                        false
% 3.30/0.98  --abstr_ref_until_sat                   false
% 3.30/0.98  --abstr_ref_sig_restrict                funpre
% 3.30/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.98  --abstr_ref_under                       []
% 3.30/0.98  
% 3.30/0.98  ------ SAT Options
% 3.30/0.98  
% 3.30/0.98  --sat_mode                              false
% 3.30/0.98  --sat_fm_restart_options                ""
% 3.30/0.98  --sat_gr_def                            false
% 3.30/0.98  --sat_epr_types                         true
% 3.30/0.98  --sat_non_cyclic_types                  false
% 3.30/0.98  --sat_finite_models                     false
% 3.30/0.98  --sat_fm_lemmas                         false
% 3.30/0.98  --sat_fm_prep                           false
% 3.30/0.98  --sat_fm_uc_incr                        true
% 3.30/0.98  --sat_out_model                         small
% 3.30/0.98  --sat_out_clauses                       false
% 3.30/0.98  
% 3.30/0.98  ------ QBF Options
% 3.30/0.98  
% 3.30/0.98  --qbf_mode                              false
% 3.30/0.98  --qbf_elim_univ                         false
% 3.30/0.98  --qbf_dom_inst                          none
% 3.30/0.98  --qbf_dom_pre_inst                      false
% 3.30/0.98  --qbf_sk_in                             false
% 3.30/0.98  --qbf_pred_elim                         true
% 3.30/0.98  --qbf_split                             512
% 3.30/0.98  
% 3.30/0.98  ------ BMC1 Options
% 3.30/0.98  
% 3.30/0.98  --bmc1_incremental                      false
% 3.30/0.98  --bmc1_axioms                           reachable_all
% 3.30/0.98  --bmc1_min_bound                        0
% 3.30/0.98  --bmc1_max_bound                        -1
% 3.30/0.98  --bmc1_max_bound_default                -1
% 3.30/0.98  --bmc1_symbol_reachability              true
% 3.30/0.98  --bmc1_property_lemmas                  false
% 3.30/0.98  --bmc1_k_induction                      false
% 3.30/0.98  --bmc1_non_equiv_states                 false
% 3.30/0.98  --bmc1_deadlock                         false
% 3.30/0.98  --bmc1_ucm                              false
% 3.30/0.98  --bmc1_add_unsat_core                   none
% 3.30/0.98  --bmc1_unsat_core_children              false
% 3.30/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.98  --bmc1_out_stat                         full
% 3.30/0.98  --bmc1_ground_init                      false
% 3.30/0.98  --bmc1_pre_inst_next_state              false
% 3.30/0.98  --bmc1_pre_inst_state                   false
% 3.30/0.98  --bmc1_pre_inst_reach_state             false
% 3.30/0.98  --bmc1_out_unsat_core                   false
% 3.30/0.98  --bmc1_aig_witness_out                  false
% 3.30/0.98  --bmc1_verbose                          false
% 3.30/0.98  --bmc1_dump_clauses_tptp                false
% 3.30/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.98  --bmc1_dump_file                        -
% 3.30/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.98  --bmc1_ucm_extend_mode                  1
% 3.30/0.98  --bmc1_ucm_init_mode                    2
% 3.30/0.98  --bmc1_ucm_cone_mode                    none
% 3.30/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.98  --bmc1_ucm_relax_model                  4
% 3.30/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.98  --bmc1_ucm_layered_model                none
% 3.30/0.98  --bmc1_ucm_max_lemma_size               10
% 3.30/0.98  
% 3.30/0.98  ------ AIG Options
% 3.30/0.98  
% 3.30/0.98  --aig_mode                              false
% 3.30/0.98  
% 3.30/0.98  ------ Instantiation Options
% 3.30/0.98  
% 3.30/0.98  --instantiation_flag                    true
% 3.30/0.98  --inst_sos_flag                         false
% 3.30/0.98  --inst_sos_phase                        true
% 3.30/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.98  --inst_lit_sel_side                     num_symb
% 3.30/0.98  --inst_solver_per_active                1400
% 3.30/0.98  --inst_solver_calls_frac                1.
% 3.30/0.98  --inst_passive_queue_type               priority_queues
% 3.30/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.98  --inst_passive_queues_freq              [25;2]
% 3.30/0.98  --inst_dismatching                      true
% 3.30/0.98  --inst_eager_unprocessed_to_passive     true
% 3.30/0.98  --inst_prop_sim_given                   true
% 3.30/0.98  --inst_prop_sim_new                     false
% 3.30/0.98  --inst_subs_new                         false
% 3.30/0.98  --inst_eq_res_simp                      false
% 3.30/0.98  --inst_subs_given                       false
% 3.30/0.98  --inst_orphan_elimination               true
% 3.30/0.98  --inst_learning_loop_flag               true
% 3.30/0.98  --inst_learning_start                   3000
% 3.30/0.98  --inst_learning_factor                  2
% 3.30/0.98  --inst_start_prop_sim_after_learn       3
% 3.30/0.98  --inst_sel_renew                        solver
% 3.30/0.98  --inst_lit_activity_flag                true
% 3.30/0.98  --inst_restr_to_given                   false
% 3.30/0.98  --inst_activity_threshold               500
% 3.30/0.98  --inst_out_proof                        true
% 3.30/0.98  
% 3.30/0.98  ------ Resolution Options
% 3.30/0.98  
% 3.30/0.98  --resolution_flag                       true
% 3.30/0.98  --res_lit_sel                           adaptive
% 3.30/0.98  --res_lit_sel_side                      none
% 3.30/0.98  --res_ordering                          kbo
% 3.30/0.98  --res_to_prop_solver                    active
% 3.30/0.98  --res_prop_simpl_new                    false
% 3.30/0.98  --res_prop_simpl_given                  true
% 3.30/0.98  --res_passive_queue_type                priority_queues
% 3.30/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.98  --res_passive_queues_freq               [15;5]
% 3.30/0.98  --res_forward_subs                      full
% 3.30/0.98  --res_backward_subs                     full
% 3.30/0.98  --res_forward_subs_resolution           true
% 3.30/0.98  --res_backward_subs_resolution          true
% 3.30/0.98  --res_orphan_elimination                true
% 3.30/0.98  --res_time_limit                        2.
% 3.30/0.98  --res_out_proof                         true
% 3.30/0.98  
% 3.30/0.98  ------ Superposition Options
% 3.30/0.98  
% 3.30/0.98  --superposition_flag                    true
% 3.30/0.98  --sup_passive_queue_type                priority_queues
% 3.30/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.98  --demod_completeness_check              fast
% 3.30/0.98  --demod_use_ground                      true
% 3.30/0.98  --sup_to_prop_solver                    passive
% 3.30/0.98  --sup_prop_simpl_new                    true
% 3.30/0.98  --sup_prop_simpl_given                  true
% 3.30/0.98  --sup_fun_splitting                     false
% 3.30/0.98  --sup_smt_interval                      50000
% 3.30/0.98  
% 3.30/0.98  ------ Superposition Simplification Setup
% 3.30/0.98  
% 3.30/0.98  --sup_indices_passive                   []
% 3.30/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.98  --sup_full_bw                           [BwDemod]
% 3.30/0.98  --sup_immed_triv                        [TrivRules]
% 3.30/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.98  --sup_immed_bw_main                     []
% 3.30/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.98  
% 3.30/0.98  ------ Combination Options
% 3.30/0.98  
% 3.30/0.98  --comb_res_mult                         3
% 3.30/0.98  --comb_sup_mult                         2
% 3.30/0.98  --comb_inst_mult                        10
% 3.30/0.98  
% 3.30/0.98  ------ Debug Options
% 3.30/0.98  
% 3.30/0.98  --dbg_backtrace                         false
% 3.30/0.98  --dbg_dump_prop_clauses                 false
% 3.30/0.98  --dbg_dump_prop_clauses_file            -
% 3.30/0.98  --dbg_out_stat                          false
% 3.30/0.98  ------ Parsing...
% 3.30/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/0.98  
% 3.30/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.30/0.98  
% 3.30/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/0.98  
% 3.30/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/0.98  ------ Proving...
% 3.30/0.98  ------ Problem Properties 
% 3.30/0.98  
% 3.30/0.98  
% 3.30/0.98  clauses                                 21
% 3.30/0.98  conjectures                             4
% 3.30/0.98  EPR                                     1
% 3.30/0.98  Horn                                    21
% 3.30/0.98  unary                                   6
% 3.30/0.98  binary                                  8
% 3.30/0.98  lits                                    45
% 3.30/0.98  lits eq                                 7
% 3.30/0.98  fd_pure                                 0
% 3.30/0.98  fd_pseudo                               0
% 3.30/0.98  fd_cond                                 0
% 3.30/0.98  fd_pseudo_cond                          0
% 3.30/0.98  AC symbols                              0
% 3.30/0.98  
% 3.30/0.98  ------ Schedule dynamic 5 is on 
% 3.30/0.98  
% 3.30/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.30/0.98  
% 3.30/0.98  
% 3.30/0.98  ------ 
% 3.30/0.98  Current options:
% 3.30/0.98  ------ 
% 3.30/0.98  
% 3.30/0.98  ------ Input Options
% 3.30/0.98  
% 3.30/0.98  --out_options                           all
% 3.30/0.98  --tptp_safe_out                         true
% 3.30/0.98  --problem_path                          ""
% 3.30/0.98  --include_path                          ""
% 3.30/0.98  --clausifier                            res/vclausify_rel
% 3.30/0.98  --clausifier_options                    --mode clausify
% 3.30/0.98  --stdin                                 false
% 3.30/0.98  --stats_out                             all
% 3.30/0.98  
% 3.30/0.98  ------ General Options
% 3.30/0.98  
% 3.30/0.98  --fof                                   false
% 3.30/0.98  --time_out_real                         305.
% 3.30/0.98  --time_out_virtual                      -1.
% 3.30/0.98  --symbol_type_check                     false
% 3.30/0.98  --clausify_out                          false
% 3.30/0.98  --sig_cnt_out                           false
% 3.30/0.98  --trig_cnt_out                          false
% 3.30/0.98  --trig_cnt_out_tolerance                1.
% 3.30/0.98  --trig_cnt_out_sk_spl                   false
% 3.30/0.98  --abstr_cl_out                          false
% 3.30/0.98  
% 3.30/0.98  ------ Global Options
% 3.30/0.98  
% 3.30/0.98  --schedule                              default
% 3.30/0.98  --add_important_lit                     false
% 3.30/0.98  --prop_solver_per_cl                    1000
% 3.30/0.98  --min_unsat_core                        false
% 3.30/0.98  --soft_assumptions                      false
% 3.30/0.98  --soft_lemma_size                       3
% 3.30/0.98  --prop_impl_unit_size                   0
% 3.30/0.98  --prop_impl_unit                        []
% 3.30/0.98  --share_sel_clauses                     true
% 3.30/0.98  --reset_solvers                         false
% 3.30/0.98  --bc_imp_inh                            [conj_cone]
% 3.30/0.98  --conj_cone_tolerance                   3.
% 3.30/0.98  --extra_neg_conj                        none
% 3.30/0.98  --large_theory_mode                     true
% 3.30/0.98  --prolific_symb_bound                   200
% 3.30/0.98  --lt_threshold                          2000
% 3.30/0.98  --clause_weak_htbl                      true
% 3.30/0.98  --gc_record_bc_elim                     false
% 3.30/0.98  
% 3.30/0.98  ------ Preprocessing Options
% 3.30/0.98  
% 3.30/0.98  --preprocessing_flag                    true
% 3.30/0.98  --time_out_prep_mult                    0.1
% 3.30/0.98  --splitting_mode                        input
% 3.30/0.98  --splitting_grd                         true
% 3.30/0.98  --splitting_cvd                         false
% 3.30/0.98  --splitting_cvd_svl                     false
% 3.30/0.98  --splitting_nvd                         32
% 3.30/0.98  --sub_typing                            true
% 3.30/0.98  --prep_gs_sim                           true
% 3.30/0.98  --prep_unflatten                        true
% 3.30/0.98  --prep_res_sim                          true
% 3.30/0.98  --prep_upred                            true
% 3.30/0.98  --prep_sem_filter                       exhaustive
% 3.30/0.98  --prep_sem_filter_out                   false
% 3.30/0.98  --pred_elim                             true
% 3.30/0.98  --res_sim_input                         true
% 3.30/0.98  --eq_ax_congr_red                       true
% 3.30/0.98  --pure_diseq_elim                       true
% 3.30/0.98  --brand_transform                       false
% 3.30/0.98  --non_eq_to_eq                          false
% 3.30/0.98  --prep_def_merge                        true
% 3.30/0.98  --prep_def_merge_prop_impl              false
% 3.30/0.98  --prep_def_merge_mbd                    true
% 3.30/0.98  --prep_def_merge_tr_red                 false
% 3.30/0.98  --prep_def_merge_tr_cl                  false
% 3.30/0.98  --smt_preprocessing                     true
% 3.30/0.98  --smt_ac_axioms                         fast
% 3.30/0.98  --preprocessed_out                      false
% 3.30/0.98  --preprocessed_stats                    false
% 3.30/0.98  
% 3.30/0.98  ------ Abstraction refinement Options
% 3.30/0.98  
% 3.30/0.98  --abstr_ref                             []
% 3.30/0.98  --abstr_ref_prep                        false
% 3.30/0.98  --abstr_ref_until_sat                   false
% 3.30/0.98  --abstr_ref_sig_restrict                funpre
% 3.30/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.30/0.98  --abstr_ref_under                       []
% 3.30/0.98  
% 3.30/0.98  ------ SAT Options
% 3.30/0.98  
% 3.30/0.98  --sat_mode                              false
% 3.30/0.98  --sat_fm_restart_options                ""
% 3.30/0.98  --sat_gr_def                            false
% 3.30/0.98  --sat_epr_types                         true
% 3.30/0.98  --sat_non_cyclic_types                  false
% 3.30/0.98  --sat_finite_models                     false
% 3.30/0.98  --sat_fm_lemmas                         false
% 3.30/0.98  --sat_fm_prep                           false
% 3.30/0.98  --sat_fm_uc_incr                        true
% 3.30/0.98  --sat_out_model                         small
% 3.30/0.98  --sat_out_clauses                       false
% 3.30/0.98  
% 3.30/0.98  ------ QBF Options
% 3.30/0.98  
% 3.30/0.98  --qbf_mode                              false
% 3.30/0.98  --qbf_elim_univ                         false
% 3.30/0.98  --qbf_dom_inst                          none
% 3.30/0.98  --qbf_dom_pre_inst                      false
% 3.30/0.98  --qbf_sk_in                             false
% 3.30/0.98  --qbf_pred_elim                         true
% 3.30/0.98  --qbf_split                             512
% 3.30/0.98  
% 3.30/0.98  ------ BMC1 Options
% 3.30/0.98  
% 3.30/0.98  --bmc1_incremental                      false
% 3.30/0.98  --bmc1_axioms                           reachable_all
% 3.30/0.98  --bmc1_min_bound                        0
% 3.30/0.98  --bmc1_max_bound                        -1
% 3.30/0.98  --bmc1_max_bound_default                -1
% 3.30/0.98  --bmc1_symbol_reachability              true
% 3.30/0.98  --bmc1_property_lemmas                  false
% 3.30/0.98  --bmc1_k_induction                      false
% 3.30/0.98  --bmc1_non_equiv_states                 false
% 3.30/0.98  --bmc1_deadlock                         false
% 3.30/0.98  --bmc1_ucm                              false
% 3.30/0.98  --bmc1_add_unsat_core                   none
% 3.30/0.98  --bmc1_unsat_core_children              false
% 3.30/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.30/0.98  --bmc1_out_stat                         full
% 3.30/0.98  --bmc1_ground_init                      false
% 3.30/0.98  --bmc1_pre_inst_next_state              false
% 3.30/0.98  --bmc1_pre_inst_state                   false
% 3.30/0.98  --bmc1_pre_inst_reach_state             false
% 3.30/0.98  --bmc1_out_unsat_core                   false
% 3.30/0.98  --bmc1_aig_witness_out                  false
% 3.30/0.98  --bmc1_verbose                          false
% 3.30/0.98  --bmc1_dump_clauses_tptp                false
% 3.30/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.30/0.98  --bmc1_dump_file                        -
% 3.30/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.30/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.30/0.98  --bmc1_ucm_extend_mode                  1
% 3.30/0.98  --bmc1_ucm_init_mode                    2
% 3.30/0.98  --bmc1_ucm_cone_mode                    none
% 3.30/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.30/0.98  --bmc1_ucm_relax_model                  4
% 3.30/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.30/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.30/0.98  --bmc1_ucm_layered_model                none
% 3.30/0.98  --bmc1_ucm_max_lemma_size               10
% 3.30/0.98  
% 3.30/0.98  ------ AIG Options
% 3.30/0.98  
% 3.30/0.98  --aig_mode                              false
% 3.30/0.98  
% 3.30/0.98  ------ Instantiation Options
% 3.30/0.98  
% 3.30/0.98  --instantiation_flag                    true
% 3.30/0.98  --inst_sos_flag                         false
% 3.30/0.98  --inst_sos_phase                        true
% 3.30/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.30/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.30/0.98  --inst_lit_sel_side                     none
% 3.30/0.98  --inst_solver_per_active                1400
% 3.30/0.98  --inst_solver_calls_frac                1.
% 3.30/0.98  --inst_passive_queue_type               priority_queues
% 3.30/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.30/0.98  --inst_passive_queues_freq              [25;2]
% 3.30/0.98  --inst_dismatching                      true
% 3.30/0.98  --inst_eager_unprocessed_to_passive     true
% 3.30/0.98  --inst_prop_sim_given                   true
% 3.30/0.98  --inst_prop_sim_new                     false
% 3.30/0.98  --inst_subs_new                         false
% 3.30/0.98  --inst_eq_res_simp                      false
% 3.30/0.98  --inst_subs_given                       false
% 3.30/0.98  --inst_orphan_elimination               true
% 3.30/0.98  --inst_learning_loop_flag               true
% 3.30/0.98  --inst_learning_start                   3000
% 3.30/0.98  --inst_learning_factor                  2
% 3.30/0.98  --inst_start_prop_sim_after_learn       3
% 3.30/0.98  --inst_sel_renew                        solver
% 3.30/0.98  --inst_lit_activity_flag                true
% 3.30/0.98  --inst_restr_to_given                   false
% 3.30/0.98  --inst_activity_threshold               500
% 3.30/0.98  --inst_out_proof                        true
% 3.30/0.98  
% 3.30/0.98  ------ Resolution Options
% 3.30/0.98  
% 3.30/0.98  --resolution_flag                       false
% 3.30/0.98  --res_lit_sel                           adaptive
% 3.30/0.98  --res_lit_sel_side                      none
% 3.30/0.98  --res_ordering                          kbo
% 3.30/0.98  --res_to_prop_solver                    active
% 3.30/0.98  --res_prop_simpl_new                    false
% 3.30/0.98  --res_prop_simpl_given                  true
% 3.30/0.98  --res_passive_queue_type                priority_queues
% 3.30/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.30/0.98  --res_passive_queues_freq               [15;5]
% 3.30/0.98  --res_forward_subs                      full
% 3.30/0.98  --res_backward_subs                     full
% 3.30/0.98  --res_forward_subs_resolution           true
% 3.30/0.98  --res_backward_subs_resolution          true
% 3.30/0.98  --res_orphan_elimination                true
% 3.30/0.98  --res_time_limit                        2.
% 3.30/0.98  --res_out_proof                         true
% 3.30/0.98  
% 3.30/0.98  ------ Superposition Options
% 3.30/0.98  
% 3.30/0.98  --superposition_flag                    true
% 3.30/0.98  --sup_passive_queue_type                priority_queues
% 3.30/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.30/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.30/0.98  --demod_completeness_check              fast
% 3.30/0.98  --demod_use_ground                      true
% 3.30/0.98  --sup_to_prop_solver                    passive
% 3.30/0.98  --sup_prop_simpl_new                    true
% 3.30/0.98  --sup_prop_simpl_given                  true
% 3.30/0.98  --sup_fun_splitting                     false
% 3.30/0.98  --sup_smt_interval                      50000
% 3.30/0.98  
% 3.30/0.98  ------ Superposition Simplification Setup
% 3.30/0.98  
% 3.30/0.98  --sup_indices_passive                   []
% 3.30/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.30/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.30/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.98  --sup_full_bw                           [BwDemod]
% 3.30/0.98  --sup_immed_triv                        [TrivRules]
% 3.30/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.30/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.98  --sup_immed_bw_main                     []
% 3.30/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.30/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.30/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.30/0.98  
% 3.30/0.98  ------ Combination Options
% 3.30/0.98  
% 3.30/0.98  --comb_res_mult                         3
% 3.30/0.98  --comb_sup_mult                         2
% 3.30/0.98  --comb_inst_mult                        10
% 3.30/0.98  
% 3.30/0.98  ------ Debug Options
% 3.30/0.98  
% 3.30/0.98  --dbg_backtrace                         false
% 3.30/0.98  --dbg_dump_prop_clauses                 false
% 3.30/0.98  --dbg_dump_prop_clauses_file            -
% 3.30/0.98  --dbg_out_stat                          false
% 3.30/0.98  
% 3.30/0.98  
% 3.30/0.98  
% 3.30/0.98  
% 3.30/0.98  ------ Proving...
% 3.30/0.98  
% 3.30/0.98  
% 3.30/0.98  % SZS status Theorem for theBenchmark.p
% 3.30/0.98  
% 3.30/0.98   Resolution empty clause
% 3.30/0.98  
% 3.30/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/0.98  
% 3.30/0.98  fof(f8,axiom,(
% 3.30/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.98  
% 3.30/0.98  fof(f24,plain,(
% 3.30/0.98    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.30/0.98    inference(ennf_transformation,[],[f8])).
% 3.30/0.98  
% 3.30/0.98  fof(f54,plain,(
% 3.30/0.98    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.30/0.98    inference(cnf_transformation,[],[f24])).
% 3.30/0.98  
% 3.30/0.98  fof(f15,conjecture,(
% 3.30/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 3.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.98  
% 3.30/0.98  fof(f16,negated_conjecture,(
% 3.30/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 3.30/0.98    inference(negated_conjecture,[],[f15])).
% 3.30/0.98  
% 3.30/0.98  fof(f35,plain,(
% 3.30/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.30/0.98    inference(ennf_transformation,[],[f16])).
% 3.30/0.98  
% 3.30/0.98  fof(f36,plain,(
% 3.30/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.30/0.98    inference(flattening,[],[f35])).
% 3.30/0.98  
% 3.30/0.98  fof(f43,plain,(
% 3.30/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.30/0.98    introduced(choice_axiom,[])).
% 3.30/0.98  
% 3.30/0.98  fof(f42,plain,(
% 3.30/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 3.30/0.98    introduced(choice_axiom,[])).
% 3.30/0.98  
% 3.30/0.98  fof(f41,plain,(
% 3.30/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.30/0.98    introduced(choice_axiom,[])).
% 3.30/0.98  
% 3.30/0.98  fof(f40,plain,(
% 3.30/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.30/0.98    introduced(choice_axiom,[])).
% 3.30/0.98  
% 3.30/0.98  fof(f39,plain,(
% 3.30/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.30/0.98    introduced(choice_axiom,[])).
% 3.30/0.98  
% 3.30/0.98  fof(f44,plain,(
% 3.30/0.98    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.30/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f36,f43,f42,f41,f40,f39])).
% 3.30/0.98  
% 3.30/0.98  fof(f71,plain,(
% 3.30/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.30/0.98    inference(cnf_transformation,[],[f44])).
% 3.30/0.98  
% 3.30/0.98  fof(f9,axiom,(
% 3.30/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.98  
% 3.30/0.98  fof(f17,plain,(
% 3.30/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.30/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.30/0.98  
% 3.30/0.98  fof(f25,plain,(
% 3.30/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.98    inference(ennf_transformation,[],[f17])).
% 3.30/0.98  
% 3.30/0.98  fof(f55,plain,(
% 3.30/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.98    inference(cnf_transformation,[],[f25])).
% 3.30/0.98  
% 3.30/0.98  fof(f1,axiom,(
% 3.30/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.98  
% 3.30/0.98  fof(f37,plain,(
% 3.30/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.30/0.98    inference(nnf_transformation,[],[f1])).
% 3.30/0.98  
% 3.30/0.98  fof(f46,plain,(
% 3.30/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.30/0.98    inference(cnf_transformation,[],[f37])).
% 3.30/0.98  
% 3.30/0.98  fof(f3,axiom,(
% 3.30/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 3.30/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.98  
% 3.30/0.98  fof(f19,plain,(
% 3.30/0.99    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.30/0.99    inference(ennf_transformation,[],[f3])).
% 3.30/0.99  
% 3.30/0.99  fof(f20,plain,(
% 3.30/0.99    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.30/0.99    inference(flattening,[],[f19])).
% 3.30/0.99  
% 3.30/0.99  fof(f48,plain,(
% 3.30/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f20])).
% 3.30/0.99  
% 3.30/0.99  fof(f45,plain,(
% 3.30/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.30/0.99    inference(cnf_transformation,[],[f37])).
% 3.30/0.99  
% 3.30/0.99  fof(f2,axiom,(
% 3.30/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f18,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f2])).
% 3.30/0.99  
% 3.30/0.99  fof(f47,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f18])).
% 3.30/0.99  
% 3.30/0.99  fof(f6,axiom,(
% 3.30/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f52,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.30/0.99    inference(cnf_transformation,[],[f6])).
% 3.30/0.99  
% 3.30/0.99  fof(f4,axiom,(
% 3.30/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f21,plain,(
% 3.30/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.30/0.99    inference(ennf_transformation,[],[f4])).
% 3.30/0.99  
% 3.30/0.99  fof(f38,plain,(
% 3.30/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.30/0.99    inference(nnf_transformation,[],[f21])).
% 3.30/0.99  
% 3.30/0.99  fof(f49,plain,(
% 3.30/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f38])).
% 3.30/0.99  
% 3.30/0.99  fof(f7,axiom,(
% 3.30/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f23,plain,(
% 3.30/0.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.30/0.99    inference(ennf_transformation,[],[f7])).
% 3.30/0.99  
% 3.30/0.99  fof(f53,plain,(
% 3.30/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f23])).
% 3.30/0.99  
% 3.30/0.99  fof(f11,axiom,(
% 3.30/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f27,plain,(
% 3.30/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.30/0.99    inference(ennf_transformation,[],[f11])).
% 3.30/0.99  
% 3.30/0.99  fof(f28,plain,(
% 3.30/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.30/0.99    inference(flattening,[],[f27])).
% 3.30/0.99  
% 3.30/0.99  fof(f57,plain,(
% 3.30/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f28])).
% 3.30/0.99  
% 3.30/0.99  fof(f10,axiom,(
% 3.30/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f26,plain,(
% 3.30/0.99    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/0.99    inference(ennf_transformation,[],[f10])).
% 3.30/0.99  
% 3.30/0.99  fof(f56,plain,(
% 3.30/0.99    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/0.99    inference(cnf_transformation,[],[f26])).
% 3.30/0.99  
% 3.30/0.99  fof(f5,axiom,(
% 3.30/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f22,plain,(
% 3.30/0.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.30/0.99    inference(ennf_transformation,[],[f5])).
% 3.30/0.99  
% 3.30/0.99  fof(f51,plain,(
% 3.30/0.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f22])).
% 3.30/0.99  
% 3.30/0.99  fof(f12,axiom,(
% 3.30/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f29,plain,(
% 3.30/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.30/0.99    inference(ennf_transformation,[],[f12])).
% 3.30/0.99  
% 3.30/0.99  fof(f30,plain,(
% 3.30/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.30/0.99    inference(flattening,[],[f29])).
% 3.30/0.99  
% 3.30/0.99  fof(f58,plain,(
% 3.30/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f30])).
% 3.30/0.99  
% 3.30/0.99  fof(f69,plain,(
% 3.30/0.99    v1_funct_1(sK3)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f70,plain,(
% 3.30/0.99    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f14,axiom,(
% 3.30/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f33,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f14])).
% 3.30/0.99  
% 3.30/0.99  fof(f34,plain,(
% 3.30/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.30/0.99    inference(flattening,[],[f33])).
% 3.30/0.99  
% 3.30/0.99  fof(f60,plain,(
% 3.30/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f34])).
% 3.30/0.99  
% 3.30/0.99  fof(f68,plain,(
% 3.30/0.99    m1_pre_topc(sK2,sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f61,plain,(
% 3.30/0.99    ~v2_struct_0(sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f62,plain,(
% 3.30/0.99    v2_pre_topc(sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f63,plain,(
% 3.30/0.99    l1_pre_topc(sK0)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f66,plain,(
% 3.30/0.99    l1_pre_topc(sK1)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f64,plain,(
% 3.30/0.99    ~v2_struct_0(sK1)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f65,plain,(
% 3.30/0.99    v2_pre_topc(sK1)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f74,plain,(
% 3.30/0.99    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f73,plain,(
% 3.30/0.99    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 3.30/0.99    inference(cnf_transformation,[],[f44])).
% 3.30/0.99  
% 3.30/0.99  fof(f13,axiom,(
% 3.30/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.30/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.30/0.99  
% 3.30/0.99  fof(f31,plain,(
% 3.30/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.30/0.99    inference(ennf_transformation,[],[f13])).
% 3.30/0.99  
% 3.30/0.99  fof(f32,plain,(
% 3.30/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.30/0.99    inference(flattening,[],[f31])).
% 3.30/0.99  
% 3.30/0.99  fof(f59,plain,(
% 3.30/0.99    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.30/0.99    inference(cnf_transformation,[],[f32])).
% 3.30/0.99  
% 3.30/0.99  cnf(c_9,plain,
% 3.30/0.99      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1571,plain,
% 3.30/0.99      ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) | ~ v1_relat_1(X0_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2097,plain,
% 3.30/0.99      ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) = iProver_top
% 3.30/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1571]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_19,negated_conjecture,
% 3.30/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1564,negated_conjecture,
% 3.30/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2103,plain,
% 3.30/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_10,plain,
% 3.30/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.30/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1570,plain,
% 3.30/0.99      ( v5_relat_1(X0_53,X1_53)
% 3.30/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2098,plain,
% 3.30/0.99      ( v5_relat_1(X0_53,X1_53) = iProver_top
% 3.30/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1570]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2860,plain,
% 3.30/0.99      ( v5_relat_1(sK3,u1_struct_0(sK1)) = iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2103,c_2098]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_0,plain,
% 3.30/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1579,plain,
% 3.30/0.99      ( ~ r1_tarski(X0_53,X1_53) | m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2089,plain,
% 3.30/0.99      ( r1_tarski(X0_53,X1_53) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1579]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3,plain,
% 3.30/0.99      ( ~ v5_relat_1(X0,X1)
% 3.30/0.99      | v5_relat_1(X2,X1)
% 3.30/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.30/0.99      | ~ v1_relat_1(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1577,plain,
% 3.30/0.99      ( ~ v5_relat_1(X0_53,X1_53)
% 3.30/0.99      | v5_relat_1(X2_53,X1_53)
% 3.30/0.99      | ~ m1_subset_1(X2_53,k1_zfmisc_1(X0_53))
% 3.30/0.99      | ~ v1_relat_1(X0_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2091,plain,
% 3.30/0.99      ( v5_relat_1(X0_53,X1_53) != iProver_top
% 3.30/0.99      | v5_relat_1(X2_53,X1_53) = iProver_top
% 3.30/0.99      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 3.30/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1577]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2879,plain,
% 3.30/0.99      ( v5_relat_1(X0_53,X1_53) != iProver_top
% 3.30/0.99      | v5_relat_1(X2_53,X1_53) = iProver_top
% 3.30/0.99      | r1_tarski(X2_53,X0_53) != iProver_top
% 3.30/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2089,c_2091]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4213,plain,
% 3.30/0.99      ( v5_relat_1(X0_53,u1_struct_0(sK1)) = iProver_top
% 3.30/0.99      | r1_tarski(X0_53,sK3) != iProver_top
% 3.30/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2860,c_2879]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_40,plain,
% 3.30/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1,plain,
% 3.30/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1578,plain,
% 3.30/0.99      ( r1_tarski(X0_53,X1_53) | ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2265,plain,
% 3.30/0.99      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.30/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1578]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2266,plain,
% 3.30/0.99      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top
% 3.30/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_2265]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_212,plain,
% 3.30/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.30/0.99      inference(prop_impl,[status(thm)],[c_0]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_267,plain,
% 3.30/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.30/0.99      inference(bin_hyper_res,[status(thm)],[c_2,c_212]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1563,plain,
% 3.30/0.99      ( ~ r1_tarski(X0_53,X1_53) | ~ v1_relat_1(X1_53) | v1_relat_1(X0_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_267]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2247,plain,
% 3.30/0.99      ( ~ r1_tarski(X0_53,k2_zfmisc_1(X1_53,X2_53))
% 3.30/0.99      | v1_relat_1(X0_53)
% 3.30/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1563]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2575,plain,
% 3.30/0.99      ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.30/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.30/0.99      | v1_relat_1(sK3) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_2247]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2576,plain,
% 3.30/0.99      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.30/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.30/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_2575]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7,plain,
% 3.30/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1573,plain,
% 3.30/0.99      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2613,plain,
% 3.30/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 3.30/0.99      inference(instantiation,[status(thm)],[c_1573]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2614,plain,
% 3.30/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_2613]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4500,plain,
% 3.30/0.99      ( r1_tarski(X0_53,sK3) != iProver_top
% 3.30/0.99      | v5_relat_1(X0_53,u1_struct_0(sK1)) = iProver_top ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_4213,c_40,c_2266,c_2576,c_2614]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_4501,plain,
% 3.30/0.99      ( v5_relat_1(X0_53,u1_struct_0(sK1)) = iProver_top
% 3.30/0.99      | r1_tarski(X0_53,sK3) != iProver_top ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_4500]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_5,plain,
% 3.30/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1575,plain,
% 3.30/0.99      ( ~ v5_relat_1(X0_53,X1_53)
% 3.30/0.99      | r1_tarski(k2_relat_1(X0_53),X1_53)
% 3.30/0.99      | ~ v1_relat_1(X0_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2093,plain,
% 3.30/0.99      ( v5_relat_1(X0_53,X1_53) != iProver_top
% 3.30/0.99      | r1_tarski(k2_relat_1(X0_53),X1_53) = iProver_top
% 3.30/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1575]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_8,plain,
% 3.30/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1572,plain,
% 3.30/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
% 3.30/0.99      | ~ v1_relat_1(X0_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2096,plain,
% 3.30/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
% 3.30/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1572]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_12,plain,
% 3.30/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.30/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.30/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.99      | ~ v1_relat_1(X0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1568,plain,
% 3.30/0.99      ( ~ r1_tarski(k1_relat_1(X0_53),X1_53)
% 3.30/0.99      | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
% 3.30/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.30/0.99      | ~ v1_relat_1(X0_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2100,plain,
% 3.30/0.99      ( r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
% 3.30/0.99      | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
% 3.30/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
% 3.30/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_11,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1569,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.30/0.99      | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2099,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 3.30/0.99      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3046,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 3.30/0.99      | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
% 3.30/0.99      | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
% 3.30/0.99      | v1_relat_1(X2_53) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2100,c_2099]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6038,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 3.30/0.99      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 3.30/0.99      | v1_relat_1(X2_53) != iProver_top
% 3.30/0.99      | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2096,c_3046]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_6,plain,
% 3.30/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1574,plain,
% 3.30/0.99      ( ~ v1_relat_1(X0_53) | v1_relat_1(k7_relat_1(X0_53,X1_53)) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2094,plain,
% 3.30/0.99      ( v1_relat_1(X0_53) != iProver_top
% 3.30/0.99      | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1574]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7524,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 3.30/0.99      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 3.30/0.99      | v1_relat_1(X2_53) != iProver_top ),
% 3.30/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_6038,c_2094]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7528,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 3.30/0.99      | v5_relat_1(k7_relat_1(X2_53,X0_53),X1_53) != iProver_top
% 3.30/0.99      | v1_relat_1(X2_53) != iProver_top
% 3.30/0.99      | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2093,c_7524]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7559,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 3.30/0.99      | v5_relat_1(k7_relat_1(X2_53,X0_53),X1_53) != iProver_top
% 3.30/0.99      | v1_relat_1(X2_53) != iProver_top ),
% 3.30/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_7528,c_2094]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7563,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(X1_53,X0_53),X2_53) = k10_relat_1(k7_relat_1(X1_53,X0_53),X2_53)
% 3.30/0.99      | r1_tarski(k7_relat_1(X1_53,X0_53),sK3) != iProver_top
% 3.30/0.99      | v1_relat_1(X1_53) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_4501,c_7559]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7678,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
% 3.30/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2097,c_7563]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7683,plain,
% 3.30/0.99      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_7678,c_40,c_2266,c_2576,c_2614]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3025,plain,
% 3.30/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2103,c_2099]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_13,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.99      | ~ v1_funct_1(X0)
% 3.30/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_21,negated_conjecture,
% 3.30/0.99      ( v1_funct_1(sK3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_468,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.30/0.99      | sK3 != X0 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_469,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.30/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_468]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1561,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.30/0.99      | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_469]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2106,plain,
% 3.30/0.99      ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
% 3.30/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2326,plain,
% 3.30/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_2103,c_2106]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_20,negated_conjecture,
% 3.30/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_15,plain,
% 3.30/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.30/0.99      | ~ m1_pre_topc(X3,X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ v1_funct_1(X0)
% 3.30/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.30/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_22,negated_conjecture,
% 3.30/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_375,plain,
% 3.30/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(X2)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(X2)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X2)
% 3.30/0.99      | ~ v1_funct_1(X0)
% 3.30/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.30/0.99      | sK2 != X3
% 3.30/0.99      | sK0 != X1 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_376,plain,
% 3.30/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | v2_struct_0(sK0)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v2_pre_topc(sK0)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(sK0)
% 3.30/0.99      | ~ v1_funct_1(X0)
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_375]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_29,negated_conjecture,
% 3.30/0.99      ( ~ v2_struct_0(sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_28,negated_conjecture,
% 3.30/0.99      ( v2_pre_topc(sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_27,negated_conjecture,
% 3.30/0.99      ( l1_pre_topc(sK0) ),
% 3.30/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_380,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X1)
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.30/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ v1_funct_1(X0)
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_376,c_29,c_28,c_27]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_381,plain,
% 3.30/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.30/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ v1_funct_1(X0)
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_380]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_416,plain,
% 3.30/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.30/0.99      | v2_struct_0(X1)
% 3.30/0.99      | ~ v2_pre_topc(X1)
% 3.30/0.99      | ~ l1_pre_topc(X1)
% 3.30/0.99      | ~ v1_funct_1(X0)
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
% 3.30/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.30/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.30/0.99      | sK3 != X0 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_381]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_417,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ v2_pre_topc(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | ~ v1_funct_1(sK3)
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 3.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_421,plain,
% 3.30/0.99      ( ~ l1_pre_topc(X0)
% 3.30/0.99      | ~ v2_pre_topc(X0)
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 3.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 3.30/0.99      inference(global_propositional_subsumption,[status(thm)],[c_417,c_21]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_422,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ v2_pre_topc(X0)
% 3.30/0.99      | ~ l1_pre_topc(X0)
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 3.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 3.30/0.99      inference(renaming,[status(thm)],[c_421]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_24,negated_conjecture,
% 3.30/0.99      ( l1_pre_topc(sK1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_487,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.30/0.99      | v2_struct_0(X0)
% 3.30/0.99      | ~ v2_pre_topc(X0)
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 3.30/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.30/0.99      | sK1 != X0 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_422,c_24]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_488,plain,
% 3.30/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.30/0.99      | v2_struct_0(sK1)
% 3.30/0.99      | ~ v2_pre_topc(sK1)
% 3.30/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 3.30/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_487]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_26,negated_conjecture,
% 3.30/0.99      ( ~ v2_struct_0(sK1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_25,negated_conjecture,
% 3.30/0.99      ( v2_pre_topc(sK1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_490,plain,
% 3.30/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 3.30/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_488,c_26,c_25,c_19]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_987,plain,
% 3.30/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 3.30/0.99      inference(equality_resolution_simp,[status(thm)],[c_490]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1559,plain,
% 3.30/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_987]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2358,plain,
% 3.30/0.99      ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_2326,c_1559]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_16,negated_conjecture,
% 3.30/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 3.30/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1567,negated_conjecture,
% 3.30/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2748,plain,
% 3.30/0.99      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_2358,c_1567]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3205,plain,
% 3.30/0.99      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_3025,c_2748]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7687,plain,
% 3.30/0.99      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_7683,c_3205]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_17,negated_conjecture,
% 3.30/0.99      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 3.30/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1566,negated_conjecture,
% 3.30/0.99      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2101,plain,
% 3.30/0.99      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1566]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3206,plain,
% 3.30/0.99      ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 3.30/0.99      inference(demodulation,[status(thm)],[c_3025,c_2101]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_14,plain,
% 3.30/0.99      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 3.30/0.99      | ~ v1_funct_1(X0)
% 3.30/0.99      | ~ v1_relat_1(X0)
% 3.30/0.99      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
% 3.30/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_453,plain,
% 3.30/0.99      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 3.30/0.99      | ~ v1_relat_1(X0)
% 3.30/0.99      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
% 3.30/0.99      | sK3 != X0 ),
% 3.30/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_454,plain,
% 3.30/0.99      ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
% 3.30/0.99      | ~ v1_relat_1(sK3)
% 3.30/0.99      | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
% 3.30/0.99      inference(unflattening,[status(thm)],[c_453]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_1562,plain,
% 3.30/0.99      ( ~ r1_tarski(k10_relat_1(sK3,X0_53),X1_53)
% 3.30/0.99      | ~ v1_relat_1(sK3)
% 3.30/0.99      | k10_relat_1(k7_relat_1(sK3,X1_53),X0_53) = k10_relat_1(sK3,X0_53) ),
% 3.30/0.99      inference(subtyping,[status(esa)],[c_454]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_2105,plain,
% 3.30/0.99      ( k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(sK3,X1_53)
% 3.30/0.99      | r1_tarski(k10_relat_1(sK3,X1_53),X0_53) != iProver_top
% 3.30/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.30/0.99      inference(predicate_to_equality,[status(thm)],[c_1562]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3252,plain,
% 3.30/0.99      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4)
% 3.30/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.30/0.99      inference(superposition,[status(thm)],[c_3206,c_2105]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_3427,plain,
% 3.30/0.99      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
% 3.30/0.99      inference(global_propositional_subsumption,
% 3.30/0.99                [status(thm)],
% 3.30/0.99                [c_3252,c_40,c_2266,c_2576,c_2614]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7688,plain,
% 3.30/0.99      ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
% 3.30/0.99      inference(light_normalisation,[status(thm)],[c_7687,c_3427]) ).
% 3.30/0.99  
% 3.30/0.99  cnf(c_7689,plain,
% 3.30/0.99      ( $false ),
% 3.30/0.99      inference(equality_resolution_simp,[status(thm)],[c_7688]) ).
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/0.99  
% 3.30/0.99  ------                               Statistics
% 3.30/0.99  
% 3.30/0.99  ------ General
% 3.30/0.99  
% 3.30/0.99  abstr_ref_over_cycles:                  0
% 3.30/0.99  abstr_ref_under_cycles:                 0
% 3.30/0.99  gc_basic_clause_elim:                   0
% 3.30/0.99  forced_gc_time:                         0
% 3.30/0.99  parsing_time:                           0.01
% 3.30/0.99  unif_index_cands_time:                  0.
% 3.30/0.99  unif_index_add_time:                    0.
% 3.30/0.99  orderings_time:                         0.
% 3.30/0.99  out_proof_time:                         0.013
% 3.30/0.99  total_time:                             0.243
% 3.30/0.99  num_of_symbols:                         59
% 3.30/0.99  num_of_terms:                           7938
% 3.30/0.99  
% 3.30/0.99  ------ Preprocessing
% 3.30/0.99  
% 3.30/0.99  num_of_splits:                          0
% 3.30/0.99  num_of_split_atoms:                     0
% 3.30/0.99  num_of_reused_defs:                     0
% 3.30/0.99  num_eq_ax_congr_red:                    21
% 3.30/0.99  num_of_sem_filtered_clauses:            1
% 3.30/0.99  num_of_subtypes:                        3
% 3.30/0.99  monotx_restored_types:                  0
% 3.30/0.99  sat_num_of_epr_types:                   0
% 3.30/0.99  sat_num_of_non_cyclic_types:            0
% 3.30/0.99  sat_guarded_non_collapsed_types:        0
% 3.30/0.99  num_pure_diseq_elim:                    0
% 3.30/0.99  simp_replaced_by:                       0
% 3.30/0.99  res_preprocessed:                       122
% 3.30/0.99  prep_upred:                             0
% 3.30/0.99  prep_unflattend:                        43
% 3.30/0.99  smt_new_axioms:                         0
% 3.30/0.99  pred_elim_cands:                        4
% 3.30/0.99  pred_elim:                              6
% 3.30/0.99  pred_elim_cl:                           9
% 3.30/0.99  pred_elim_cycles:                       8
% 3.30/0.99  merged_defs:                            8
% 3.30/0.99  merged_defs_ncl:                        0
% 3.30/0.99  bin_hyper_res:                          9
% 3.30/0.99  prep_cycles:                            4
% 3.30/0.99  pred_elim_time:                         0.022
% 3.30/0.99  splitting_time:                         0.
% 3.30/0.99  sem_filter_time:                        0.
% 3.30/0.99  monotx_time:                            0.
% 3.30/0.99  subtype_inf_time:                       0.
% 3.30/0.99  
% 3.30/0.99  ------ Problem properties
% 3.30/0.99  
% 3.30/0.99  clauses:                                21
% 3.30/0.99  conjectures:                            4
% 3.30/0.99  epr:                                    1
% 3.30/0.99  horn:                                   21
% 3.30/0.99  ground:                                 6
% 3.30/0.99  unary:                                  6
% 3.30/0.99  binary:                                 8
% 3.30/0.99  lits:                                   45
% 3.30/0.99  lits_eq:                                7
% 3.30/0.99  fd_pure:                                0
% 3.30/0.99  fd_pseudo:                              0
% 3.30/0.99  fd_cond:                                0
% 3.30/0.99  fd_pseudo_cond:                         0
% 3.30/0.99  ac_symbols:                             0
% 3.30/0.99  
% 3.30/0.99  ------ Propositional Solver
% 3.30/0.99  
% 3.30/0.99  prop_solver_calls:                      30
% 3.30/0.99  prop_fast_solver_calls:                 1084
% 3.30/0.99  smt_solver_calls:                       0
% 3.30/0.99  smt_fast_solver_calls:                  0
% 3.30/0.99  prop_num_of_clauses:                    2543
% 3.30/0.99  prop_preprocess_simplified:             6594
% 3.30/0.99  prop_fo_subsumed:                       27
% 3.30/0.99  prop_solver_time:                       0.
% 3.30/0.99  smt_solver_time:                        0.
% 3.30/0.99  smt_fast_solver_time:                   0.
% 3.30/0.99  prop_fast_solver_time:                  0.
% 3.30/0.99  prop_unsat_core_time:                   0.
% 3.30/0.99  
% 3.30/0.99  ------ QBF
% 3.30/0.99  
% 3.30/0.99  qbf_q_res:                              0
% 3.30/0.99  qbf_num_tautologies:                    0
% 3.30/0.99  qbf_prep_cycles:                        0
% 3.30/0.99  
% 3.30/0.99  ------ BMC1
% 3.30/0.99  
% 3.30/0.99  bmc1_current_bound:                     -1
% 3.30/0.99  bmc1_last_solved_bound:                 -1
% 3.30/0.99  bmc1_unsat_core_size:                   -1
% 3.30/0.99  bmc1_unsat_core_parents_size:           -1
% 3.30/0.99  bmc1_merge_next_fun:                    0
% 3.30/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.30/0.99  
% 3.30/0.99  ------ Instantiation
% 3.30/0.99  
% 3.30/0.99  inst_num_of_clauses:                    680
% 3.30/0.99  inst_num_in_passive:                    173
% 3.30/0.99  inst_num_in_active:                     428
% 3.30/0.99  inst_num_in_unprocessed:                79
% 3.30/0.99  inst_num_of_loops:                      460
% 3.30/0.99  inst_num_of_learning_restarts:          0
% 3.30/0.99  inst_num_moves_active_passive:          28
% 3.30/0.99  inst_lit_activity:                      0
% 3.30/0.99  inst_lit_activity_moves:                0
% 3.30/0.99  inst_num_tautologies:                   0
% 3.30/0.99  inst_num_prop_implied:                  0
% 3.30/0.99  inst_num_existing_simplified:           0
% 3.30/0.99  inst_num_eq_res_simplified:             0
% 3.30/0.99  inst_num_child_elim:                    0
% 3.30/0.99  inst_num_of_dismatching_blockings:      226
% 3.30/0.99  inst_num_of_non_proper_insts:           774
% 3.30/0.99  inst_num_of_duplicates:                 0
% 3.30/0.99  inst_inst_num_from_inst_to_res:         0
% 3.30/0.99  inst_dismatching_checking_time:         0.
% 3.30/0.99  
% 3.30/0.99  ------ Resolution
% 3.30/0.99  
% 3.30/0.99  res_num_of_clauses:                     0
% 3.30/0.99  res_num_in_passive:                     0
% 3.30/0.99  res_num_in_active:                      0
% 3.30/0.99  res_num_of_loops:                       126
% 3.30/0.99  res_forward_subset_subsumed:            105
% 3.30/0.99  res_backward_subset_subsumed:           0
% 3.30/0.99  res_forward_subsumed:                   0
% 3.30/0.99  res_backward_subsumed:                  0
% 3.30/0.99  res_forward_subsumption_resolution:     0
% 3.30/0.99  res_backward_subsumption_resolution:    0
% 3.30/0.99  res_clause_to_clause_subsumption:       645
% 3.30/0.99  res_orphan_elimination:                 0
% 3.30/0.99  res_tautology_del:                      129
% 3.30/0.99  res_num_eq_res_simplified:              1
% 3.30/0.99  res_num_sel_changes:                    0
% 3.30/0.99  res_moves_from_active_to_pass:          0
% 3.30/0.99  
% 3.30/0.99  ------ Superposition
% 3.30/0.99  
% 3.30/0.99  sup_time_total:                         0.
% 3.30/0.99  sup_time_generating:                    0.
% 3.30/0.99  sup_time_sim_full:                      0.
% 3.30/0.99  sup_time_sim_immed:                     0.
% 3.30/0.99  
% 3.30/0.99  sup_num_of_clauses:                     141
% 3.30/0.99  sup_num_in_active:                      86
% 3.30/0.99  sup_num_in_passive:                     55
% 3.30/0.99  sup_num_of_loops:                       91
% 3.30/0.99  sup_fw_superposition:                   86
% 3.30/0.99  sup_bw_superposition:                   49
% 3.30/0.99  sup_immediate_simplified:               4
% 3.30/0.99  sup_given_eliminated:                   0
% 3.30/0.99  comparisons_done:                       0
% 3.30/0.99  comparisons_avoided:                    0
% 3.30/0.99  
% 3.30/0.99  ------ Simplifications
% 3.30/0.99  
% 3.30/0.99  
% 3.30/0.99  sim_fw_subset_subsumed:                 3
% 3.30/0.99  sim_bw_subset_subsumed:                 0
% 3.30/0.99  sim_fw_subsumed:                        1
% 3.30/0.99  sim_bw_subsumed:                        0
% 3.30/0.99  sim_fw_subsumption_res:                 3
% 3.30/0.99  sim_bw_subsumption_res:                 0
% 3.30/0.99  sim_tautology_del:                      3
% 3.30/0.99  sim_eq_tautology_del:                   0
% 3.30/0.99  sim_eq_res_simp:                        0
% 3.30/0.99  sim_fw_demodulated:                     0
% 3.30/0.99  sim_bw_demodulated:                     5
% 3.30/0.99  sim_light_normalised:                   1
% 3.30/0.99  sim_joinable_taut:                      0
% 3.30/0.99  sim_joinable_simp:                      0
% 3.30/0.99  sim_ac_normalised:                      0
% 3.30/0.99  sim_smt_subsumption:                    0
% 3.30/0.99  
%------------------------------------------------------------------------------
