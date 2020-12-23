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
% DateTime   : Thu Dec  3 12:22:36 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 514 expanded)
%              Number of clauses        :  106 ( 178 expanded)
%              Number of leaves         :   20 ( 164 expanded)
%              Depth                    :   25
%              Number of atoms          :  631 (4242 expanded)
%              Number of equality atoms :  156 ( 524 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4)
        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f38,f44,f43,f42,f41,f40])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1073,plain,
    ( ~ v1_relat_1(X0_53)
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1402,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1073])).

cnf(c_9,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1068,plain,
    ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1407,plain,
    ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1068])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1071,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | r1_tarski(k2_relat_1(X0_53),k2_relat_1(X1_53))
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1404,plain,
    ( r1_tarski(X0_53,X1_53) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),k2_relat_1(X1_53)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1062,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1412,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_3])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | r1_tarski(k2_relat_1(X0_53),X2_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_1413,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_2396,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1412,c_1413])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0_53))
    | ~ v1_relat_1(X0_53)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_1487,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_1624,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_1625,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1624])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1072,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1658,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_1659,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1658])).

cnf(c_1998,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | r1_tarski(k2_relat_1(sK3),X1_53)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_2346,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_2347,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2346])).

cnf(c_2400,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2396,c_40,c_1625,c_1659,c_2347])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1075,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | ~ r1_tarski(X2_53,X0_53)
    | r1_tarski(X2_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1400,plain,
    ( r1_tarski(X0_53,X1_53) != iProver_top
    | r1_tarski(X2_53,X0_53) != iProver_top
    | r1_tarski(X2_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1075])).

cnf(c_2404,plain,
    ( r1_tarski(X0_53,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0_53,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2400,c_1400])).

cnf(c_2468,plain,
    ( r1_tarski(X0_53,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_2404])).

cnf(c_2902,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0_53,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2468,c_40,c_1625,c_1659])).

cnf(c_2903,plain,
    ( r1_tarski(X0_53,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2902])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1069,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1406,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1069])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1066,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ r1_tarski(k1_relat_1(X0_53),X1_53)
    | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1409,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
    | r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1067,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1408,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_2078,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
    | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1409,c_1408])).

cnf(c_7342,plain,
    ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top
    | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_2078])).

cnf(c_20441,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(X1_53,X0_53),X2_53) = k10_relat_1(k7_relat_1(X1_53,X0_53),X2_53)
    | r1_tarski(k7_relat_1(X1_53,X0_53),sK3) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(k7_relat_1(X1_53,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2903,c_7342])).

cnf(c_21141,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
    | v1_relat_1(k7_relat_1(sK3,X0_53)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_20441])).

cnf(c_21996,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0_53)) != iProver_top
    | k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21141,c_40,c_1625,c_1659])).

cnf(c_21997,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
    | v1_relat_1(k7_relat_1(sK3,X0_53)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21996])).

cnf(c_22002,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_21997])).

cnf(c_22150,plain,
    ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22002,c_40,c_1625,c_1659])).

cnf(c_2010,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_1412,c_1408])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_1059,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
    inference(subtyping,[status(esa)],[c_428])).

cnf(c_1415,plain,
    ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1059])).

cnf(c_1570,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_1412,c_1415])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_334,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_335,plain,
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
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_339,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_29,c_28,c_27])).

cnf(c_340,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_339])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_340])).

cnf(c_376,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_380,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_21])).

cnf(c_381,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_380])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_446,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_24])).

cnf(c_447,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_449,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_26,c_25,c_19])).

cnf(c_734,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_449])).

cnf(c_1057,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_734])).

cnf(c_1618,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_1570,c_1057])).

cnf(c_16,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1065,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1794,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1618,c_1065])).

cnf(c_2151,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2010,c_1794])).

cnf(c_22153,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_22150,c_2151])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1064,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1410,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1064])).

cnf(c_2153,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2010,c_1410])).

cnf(c_14,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_412,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_413,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_1060,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0_53),X1_53)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X1_53),X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(subtyping,[status(esa)],[c_413])).

cnf(c_1414,plain,
    ( k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(sK3,X1_53)
    | r1_tarski(k10_relat_1(sK3,X1_53),X0_53) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1060])).

cnf(c_2254,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2153,c_1414])).

cnf(c_2359,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2254,c_40,c_1625,c_1659])).

cnf(c_22154,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_22153,c_2359])).

cnf(c_22155,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22154])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:54:15 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 7.74/1.58  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/1.58  
% 7.74/1.58  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.74/1.58  
% 7.74/1.58  ------  iProver source info
% 7.74/1.58  
% 7.74/1.58  git: date: 2020-06-30 10:37:57 +0100
% 7.74/1.58  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.74/1.58  git: non_committed_changes: false
% 7.74/1.58  git: last_make_outside_of_git: false
% 7.74/1.58  
% 7.74/1.58  ------ 
% 7.74/1.58  
% 7.74/1.58  ------ Input Options
% 7.74/1.58  
% 7.74/1.58  --out_options                           all
% 7.74/1.58  --tptp_safe_out                         true
% 7.74/1.58  --problem_path                          ""
% 7.74/1.58  --include_path                          ""
% 7.74/1.58  --clausifier                            res/vclausify_rel
% 7.74/1.58  --clausifier_options                    ""
% 7.74/1.58  --stdin                                 false
% 7.74/1.58  --stats_out                             all
% 7.74/1.58  
% 7.74/1.58  ------ General Options
% 7.74/1.58  
% 7.74/1.58  --fof                                   false
% 7.74/1.58  --time_out_real                         305.
% 7.74/1.58  --time_out_virtual                      -1.
% 7.74/1.58  --symbol_type_check                     false
% 7.74/1.58  --clausify_out                          false
% 7.74/1.58  --sig_cnt_out                           false
% 7.74/1.58  --trig_cnt_out                          false
% 7.74/1.58  --trig_cnt_out_tolerance                1.
% 7.74/1.58  --trig_cnt_out_sk_spl                   false
% 7.74/1.58  --abstr_cl_out                          false
% 7.74/1.58  
% 7.74/1.58  ------ Global Options
% 7.74/1.58  
% 7.74/1.58  --schedule                              default
% 7.74/1.58  --add_important_lit                     false
% 7.74/1.58  --prop_solver_per_cl                    1000
% 7.74/1.58  --min_unsat_core                        false
% 7.74/1.58  --soft_assumptions                      false
% 7.74/1.58  --soft_lemma_size                       3
% 7.74/1.58  --prop_impl_unit_size                   0
% 7.74/1.58  --prop_impl_unit                        []
% 7.74/1.58  --share_sel_clauses                     true
% 7.74/1.58  --reset_solvers                         false
% 7.74/1.58  --bc_imp_inh                            [conj_cone]
% 7.74/1.58  --conj_cone_tolerance                   3.
% 7.74/1.58  --extra_neg_conj                        none
% 7.74/1.58  --large_theory_mode                     true
% 7.74/1.58  --prolific_symb_bound                   200
% 7.74/1.58  --lt_threshold                          2000
% 7.74/1.58  --clause_weak_htbl                      true
% 7.74/1.58  --gc_record_bc_elim                     false
% 7.74/1.58  
% 7.74/1.58  ------ Preprocessing Options
% 7.74/1.58  
% 7.74/1.58  --preprocessing_flag                    true
% 7.74/1.58  --time_out_prep_mult                    0.1
% 7.74/1.58  --splitting_mode                        input
% 7.74/1.58  --splitting_grd                         true
% 7.74/1.58  --splitting_cvd                         false
% 7.74/1.58  --splitting_cvd_svl                     false
% 7.74/1.58  --splitting_nvd                         32
% 7.74/1.58  --sub_typing                            true
% 7.74/1.58  --prep_gs_sim                           true
% 7.74/1.58  --prep_unflatten                        true
% 7.74/1.58  --prep_res_sim                          true
% 7.74/1.58  --prep_upred                            true
% 7.74/1.58  --prep_sem_filter                       exhaustive
% 7.74/1.58  --prep_sem_filter_out                   false
% 7.74/1.58  --pred_elim                             true
% 7.74/1.58  --res_sim_input                         true
% 7.74/1.58  --eq_ax_congr_red                       true
% 7.74/1.58  --pure_diseq_elim                       true
% 7.74/1.58  --brand_transform                       false
% 7.74/1.58  --non_eq_to_eq                          false
% 7.74/1.58  --prep_def_merge                        true
% 7.74/1.58  --prep_def_merge_prop_impl              false
% 7.74/1.58  --prep_def_merge_mbd                    true
% 7.74/1.58  --prep_def_merge_tr_red                 false
% 7.74/1.58  --prep_def_merge_tr_cl                  false
% 7.74/1.58  --smt_preprocessing                     true
% 7.74/1.58  --smt_ac_axioms                         fast
% 7.74/1.58  --preprocessed_out                      false
% 7.74/1.58  --preprocessed_stats                    false
% 7.74/1.58  
% 7.74/1.58  ------ Abstraction refinement Options
% 7.74/1.58  
% 7.74/1.58  --abstr_ref                             []
% 7.74/1.58  --abstr_ref_prep                        false
% 7.74/1.58  --abstr_ref_until_sat                   false
% 7.74/1.58  --abstr_ref_sig_restrict                funpre
% 7.74/1.58  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.58  --abstr_ref_under                       []
% 7.74/1.58  
% 7.74/1.58  ------ SAT Options
% 7.74/1.58  
% 7.74/1.58  --sat_mode                              false
% 7.74/1.58  --sat_fm_restart_options                ""
% 7.74/1.58  --sat_gr_def                            false
% 7.74/1.58  --sat_epr_types                         true
% 7.74/1.58  --sat_non_cyclic_types                  false
% 7.74/1.58  --sat_finite_models                     false
% 7.74/1.58  --sat_fm_lemmas                         false
% 7.74/1.58  --sat_fm_prep                           false
% 7.74/1.58  --sat_fm_uc_incr                        true
% 7.74/1.58  --sat_out_model                         small
% 7.74/1.58  --sat_out_clauses                       false
% 7.74/1.58  
% 7.74/1.58  ------ QBF Options
% 7.74/1.58  
% 7.74/1.58  --qbf_mode                              false
% 7.74/1.58  --qbf_elim_univ                         false
% 7.74/1.58  --qbf_dom_inst                          none
% 7.74/1.58  --qbf_dom_pre_inst                      false
% 7.74/1.58  --qbf_sk_in                             false
% 7.74/1.58  --qbf_pred_elim                         true
% 7.74/1.58  --qbf_split                             512
% 7.74/1.58  
% 7.74/1.58  ------ BMC1 Options
% 7.74/1.58  
% 7.74/1.58  --bmc1_incremental                      false
% 7.74/1.58  --bmc1_axioms                           reachable_all
% 7.74/1.58  --bmc1_min_bound                        0
% 7.74/1.58  --bmc1_max_bound                        -1
% 7.74/1.58  --bmc1_max_bound_default                -1
% 7.74/1.58  --bmc1_symbol_reachability              true
% 7.74/1.58  --bmc1_property_lemmas                  false
% 7.74/1.58  --bmc1_k_induction                      false
% 7.74/1.58  --bmc1_non_equiv_states                 false
% 7.74/1.58  --bmc1_deadlock                         false
% 7.74/1.58  --bmc1_ucm                              false
% 7.74/1.58  --bmc1_add_unsat_core                   none
% 7.74/1.58  --bmc1_unsat_core_children              false
% 7.74/1.58  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.58  --bmc1_out_stat                         full
% 7.74/1.58  --bmc1_ground_init                      false
% 7.74/1.58  --bmc1_pre_inst_next_state              false
% 7.74/1.58  --bmc1_pre_inst_state                   false
% 7.74/1.58  --bmc1_pre_inst_reach_state             false
% 7.74/1.58  --bmc1_out_unsat_core                   false
% 7.74/1.58  --bmc1_aig_witness_out                  false
% 7.74/1.58  --bmc1_verbose                          false
% 7.74/1.58  --bmc1_dump_clauses_tptp                false
% 7.74/1.58  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.58  --bmc1_dump_file                        -
% 7.74/1.58  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.58  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.58  --bmc1_ucm_extend_mode                  1
% 7.74/1.58  --bmc1_ucm_init_mode                    2
% 7.74/1.58  --bmc1_ucm_cone_mode                    none
% 7.74/1.58  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.58  --bmc1_ucm_relax_model                  4
% 7.74/1.58  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.58  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.58  --bmc1_ucm_layered_model                none
% 7.74/1.58  --bmc1_ucm_max_lemma_size               10
% 7.74/1.58  
% 7.74/1.58  ------ AIG Options
% 7.74/1.58  
% 7.74/1.58  --aig_mode                              false
% 7.74/1.58  
% 7.74/1.58  ------ Instantiation Options
% 7.74/1.58  
% 7.74/1.58  --instantiation_flag                    true
% 7.74/1.58  --inst_sos_flag                         true
% 7.74/1.58  --inst_sos_phase                        true
% 7.74/1.58  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.58  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.58  --inst_lit_sel_side                     num_symb
% 7.74/1.58  --inst_solver_per_active                1400
% 7.74/1.58  --inst_solver_calls_frac                1.
% 7.74/1.58  --inst_passive_queue_type               priority_queues
% 7.74/1.58  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.58  --inst_passive_queues_freq              [25;2]
% 7.74/1.58  --inst_dismatching                      true
% 7.74/1.58  --inst_eager_unprocessed_to_passive     true
% 7.74/1.58  --inst_prop_sim_given                   true
% 7.74/1.58  --inst_prop_sim_new                     false
% 7.74/1.58  --inst_subs_new                         false
% 7.74/1.58  --inst_eq_res_simp                      false
% 7.74/1.58  --inst_subs_given                       false
% 7.74/1.58  --inst_orphan_elimination               true
% 7.74/1.58  --inst_learning_loop_flag               true
% 7.74/1.58  --inst_learning_start                   3000
% 7.74/1.58  --inst_learning_factor                  2
% 7.74/1.58  --inst_start_prop_sim_after_learn       3
% 7.74/1.58  --inst_sel_renew                        solver
% 7.74/1.58  --inst_lit_activity_flag                true
% 7.74/1.58  --inst_restr_to_given                   false
% 7.74/1.58  --inst_activity_threshold               500
% 7.74/1.58  --inst_out_proof                        true
% 7.74/1.58  
% 7.74/1.58  ------ Resolution Options
% 7.74/1.58  
% 7.74/1.58  --resolution_flag                       true
% 7.74/1.58  --res_lit_sel                           adaptive
% 7.74/1.58  --res_lit_sel_side                      none
% 7.74/1.58  --res_ordering                          kbo
% 7.74/1.58  --res_to_prop_solver                    active
% 7.74/1.58  --res_prop_simpl_new                    false
% 7.74/1.58  --res_prop_simpl_given                  true
% 7.74/1.58  --res_passive_queue_type                priority_queues
% 7.74/1.58  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.58  --res_passive_queues_freq               [15;5]
% 7.74/1.58  --res_forward_subs                      full
% 7.74/1.58  --res_backward_subs                     full
% 7.74/1.58  --res_forward_subs_resolution           true
% 7.74/1.58  --res_backward_subs_resolution          true
% 7.74/1.58  --res_orphan_elimination                true
% 7.74/1.58  --res_time_limit                        2.
% 7.74/1.58  --res_out_proof                         true
% 7.74/1.58  
% 7.74/1.58  ------ Superposition Options
% 7.74/1.58  
% 7.74/1.58  --superposition_flag                    true
% 7.74/1.58  --sup_passive_queue_type                priority_queues
% 7.74/1.58  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.58  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.58  --demod_completeness_check              fast
% 7.74/1.58  --demod_use_ground                      true
% 7.74/1.58  --sup_to_prop_solver                    passive
% 7.74/1.58  --sup_prop_simpl_new                    true
% 7.74/1.58  --sup_prop_simpl_given                  true
% 7.74/1.58  --sup_fun_splitting                     true
% 7.74/1.58  --sup_smt_interval                      50000
% 7.74/1.58  
% 7.74/1.58  ------ Superposition Simplification Setup
% 7.74/1.58  
% 7.74/1.58  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.58  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.58  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.58  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.58  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.58  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.58  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.58  --sup_immed_triv                        [TrivRules]
% 7.74/1.58  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.58  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.58  --sup_immed_bw_main                     []
% 7.74/1.58  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.58  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.58  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.58  --sup_input_bw                          []
% 7.74/1.58  
% 7.74/1.58  ------ Combination Options
% 7.74/1.58  
% 7.74/1.58  --comb_res_mult                         3
% 7.74/1.58  --comb_sup_mult                         2
% 7.74/1.58  --comb_inst_mult                        10
% 7.74/1.58  
% 7.74/1.58  ------ Debug Options
% 7.74/1.58  
% 7.74/1.58  --dbg_backtrace                         false
% 7.74/1.58  --dbg_dump_prop_clauses                 false
% 7.74/1.58  --dbg_dump_prop_clauses_file            -
% 7.74/1.58  --dbg_out_stat                          false
% 7.74/1.58  ------ Parsing...
% 7.74/1.58  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.74/1.58  
% 7.74/1.58  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.74/1.58  
% 7.74/1.58  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.74/1.58  
% 7.74/1.58  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.74/1.58  ------ Proving...
% 7.74/1.58  ------ Problem Properties 
% 7.74/1.58  
% 7.74/1.58  
% 7.74/1.58  clauses                                 19
% 7.74/1.58  conjectures                             4
% 7.74/1.58  EPR                                     1
% 7.74/1.58  Horn                                    19
% 7.74/1.58  unary                                   6
% 7.74/1.58  binary                                  5
% 7.74/1.58  lits                                    43
% 7.74/1.58  lits eq                                 7
% 7.74/1.58  fd_pure                                 0
% 7.74/1.58  fd_pseudo                               0
% 7.74/1.58  fd_cond                                 0
% 7.74/1.58  fd_pseudo_cond                          0
% 7.74/1.58  AC symbols                              0
% 7.74/1.58  
% 7.74/1.58  ------ Schedule dynamic 5 is on 
% 7.74/1.58  
% 7.74/1.58  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.74/1.58  
% 7.74/1.58  
% 7.74/1.58  ------ 
% 7.74/1.58  Current options:
% 7.74/1.58  ------ 
% 7.74/1.58  
% 7.74/1.58  ------ Input Options
% 7.74/1.58  
% 7.74/1.58  --out_options                           all
% 7.74/1.58  --tptp_safe_out                         true
% 7.74/1.58  --problem_path                          ""
% 7.74/1.58  --include_path                          ""
% 7.74/1.58  --clausifier                            res/vclausify_rel
% 7.74/1.58  --clausifier_options                    ""
% 7.74/1.58  --stdin                                 false
% 7.74/1.58  --stats_out                             all
% 7.74/1.58  
% 7.74/1.58  ------ General Options
% 7.74/1.58  
% 7.74/1.58  --fof                                   false
% 7.74/1.58  --time_out_real                         305.
% 7.74/1.58  --time_out_virtual                      -1.
% 7.74/1.58  --symbol_type_check                     false
% 7.74/1.58  --clausify_out                          false
% 7.74/1.58  --sig_cnt_out                           false
% 7.74/1.58  --trig_cnt_out                          false
% 7.74/1.58  --trig_cnt_out_tolerance                1.
% 7.74/1.58  --trig_cnt_out_sk_spl                   false
% 7.74/1.58  --abstr_cl_out                          false
% 7.74/1.58  
% 7.74/1.58  ------ Global Options
% 7.74/1.58  
% 7.74/1.58  --schedule                              default
% 7.74/1.58  --add_important_lit                     false
% 7.74/1.58  --prop_solver_per_cl                    1000
% 7.74/1.58  --min_unsat_core                        false
% 7.74/1.58  --soft_assumptions                      false
% 7.74/1.58  --soft_lemma_size                       3
% 7.74/1.58  --prop_impl_unit_size                   0
% 7.74/1.58  --prop_impl_unit                        []
% 7.74/1.58  --share_sel_clauses                     true
% 7.74/1.58  --reset_solvers                         false
% 7.74/1.58  --bc_imp_inh                            [conj_cone]
% 7.74/1.58  --conj_cone_tolerance                   3.
% 7.74/1.58  --extra_neg_conj                        none
% 7.74/1.58  --large_theory_mode                     true
% 7.74/1.58  --prolific_symb_bound                   200
% 7.74/1.58  --lt_threshold                          2000
% 7.74/1.58  --clause_weak_htbl                      true
% 7.74/1.58  --gc_record_bc_elim                     false
% 7.74/1.58  
% 7.74/1.58  ------ Preprocessing Options
% 7.74/1.58  
% 7.74/1.58  --preprocessing_flag                    true
% 7.74/1.58  --time_out_prep_mult                    0.1
% 7.74/1.58  --splitting_mode                        input
% 7.74/1.58  --splitting_grd                         true
% 7.74/1.58  --splitting_cvd                         false
% 7.74/1.58  --splitting_cvd_svl                     false
% 7.74/1.58  --splitting_nvd                         32
% 7.74/1.58  --sub_typing                            true
% 7.74/1.58  --prep_gs_sim                           true
% 7.74/1.58  --prep_unflatten                        true
% 7.74/1.58  --prep_res_sim                          true
% 7.74/1.58  --prep_upred                            true
% 7.74/1.58  --prep_sem_filter                       exhaustive
% 7.74/1.58  --prep_sem_filter_out                   false
% 7.74/1.58  --pred_elim                             true
% 7.74/1.58  --res_sim_input                         true
% 7.74/1.58  --eq_ax_congr_red                       true
% 7.74/1.58  --pure_diseq_elim                       true
% 7.74/1.58  --brand_transform                       false
% 7.74/1.58  --non_eq_to_eq                          false
% 7.74/1.58  --prep_def_merge                        true
% 7.74/1.58  --prep_def_merge_prop_impl              false
% 7.74/1.58  --prep_def_merge_mbd                    true
% 7.74/1.58  --prep_def_merge_tr_red                 false
% 7.74/1.58  --prep_def_merge_tr_cl                  false
% 7.74/1.58  --smt_preprocessing                     true
% 7.74/1.58  --smt_ac_axioms                         fast
% 7.74/1.58  --preprocessed_out                      false
% 7.74/1.58  --preprocessed_stats                    false
% 7.74/1.58  
% 7.74/1.58  ------ Abstraction refinement Options
% 7.74/1.58  
% 7.74/1.58  --abstr_ref                             []
% 7.74/1.58  --abstr_ref_prep                        false
% 7.74/1.58  --abstr_ref_until_sat                   false
% 7.74/1.58  --abstr_ref_sig_restrict                funpre
% 7.74/1.58  --abstr_ref_af_restrict_to_split_sk     false
% 7.74/1.58  --abstr_ref_under                       []
% 7.74/1.58  
% 7.74/1.58  ------ SAT Options
% 7.74/1.58  
% 7.74/1.58  --sat_mode                              false
% 7.74/1.58  --sat_fm_restart_options                ""
% 7.74/1.58  --sat_gr_def                            false
% 7.74/1.58  --sat_epr_types                         true
% 7.74/1.58  --sat_non_cyclic_types                  false
% 7.74/1.58  --sat_finite_models                     false
% 7.74/1.58  --sat_fm_lemmas                         false
% 7.74/1.58  --sat_fm_prep                           false
% 7.74/1.58  --sat_fm_uc_incr                        true
% 7.74/1.58  --sat_out_model                         small
% 7.74/1.58  --sat_out_clauses                       false
% 7.74/1.58  
% 7.74/1.58  ------ QBF Options
% 7.74/1.58  
% 7.74/1.58  --qbf_mode                              false
% 7.74/1.58  --qbf_elim_univ                         false
% 7.74/1.58  --qbf_dom_inst                          none
% 7.74/1.58  --qbf_dom_pre_inst                      false
% 7.74/1.58  --qbf_sk_in                             false
% 7.74/1.58  --qbf_pred_elim                         true
% 7.74/1.58  --qbf_split                             512
% 7.74/1.58  
% 7.74/1.58  ------ BMC1 Options
% 7.74/1.58  
% 7.74/1.58  --bmc1_incremental                      false
% 7.74/1.58  --bmc1_axioms                           reachable_all
% 7.74/1.58  --bmc1_min_bound                        0
% 7.74/1.58  --bmc1_max_bound                        -1
% 7.74/1.58  --bmc1_max_bound_default                -1
% 7.74/1.58  --bmc1_symbol_reachability              true
% 7.74/1.58  --bmc1_property_lemmas                  false
% 7.74/1.58  --bmc1_k_induction                      false
% 7.74/1.58  --bmc1_non_equiv_states                 false
% 7.74/1.58  --bmc1_deadlock                         false
% 7.74/1.58  --bmc1_ucm                              false
% 7.74/1.58  --bmc1_add_unsat_core                   none
% 7.74/1.58  --bmc1_unsat_core_children              false
% 7.74/1.58  --bmc1_unsat_core_extrapolate_axioms    false
% 7.74/1.58  --bmc1_out_stat                         full
% 7.74/1.58  --bmc1_ground_init                      false
% 7.74/1.58  --bmc1_pre_inst_next_state              false
% 7.74/1.58  --bmc1_pre_inst_state                   false
% 7.74/1.58  --bmc1_pre_inst_reach_state             false
% 7.74/1.58  --bmc1_out_unsat_core                   false
% 7.74/1.58  --bmc1_aig_witness_out                  false
% 7.74/1.58  --bmc1_verbose                          false
% 7.74/1.58  --bmc1_dump_clauses_tptp                false
% 7.74/1.58  --bmc1_dump_unsat_core_tptp             false
% 7.74/1.58  --bmc1_dump_file                        -
% 7.74/1.58  --bmc1_ucm_expand_uc_limit              128
% 7.74/1.58  --bmc1_ucm_n_expand_iterations          6
% 7.74/1.58  --bmc1_ucm_extend_mode                  1
% 7.74/1.58  --bmc1_ucm_init_mode                    2
% 7.74/1.58  --bmc1_ucm_cone_mode                    none
% 7.74/1.58  --bmc1_ucm_reduced_relation_type        0
% 7.74/1.58  --bmc1_ucm_relax_model                  4
% 7.74/1.58  --bmc1_ucm_full_tr_after_sat            true
% 7.74/1.58  --bmc1_ucm_expand_neg_assumptions       false
% 7.74/1.58  --bmc1_ucm_layered_model                none
% 7.74/1.58  --bmc1_ucm_max_lemma_size               10
% 7.74/1.58  
% 7.74/1.58  ------ AIG Options
% 7.74/1.58  
% 7.74/1.58  --aig_mode                              false
% 7.74/1.58  
% 7.74/1.58  ------ Instantiation Options
% 7.74/1.58  
% 7.74/1.58  --instantiation_flag                    true
% 7.74/1.58  --inst_sos_flag                         true
% 7.74/1.58  --inst_sos_phase                        true
% 7.74/1.58  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.74/1.58  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.74/1.58  --inst_lit_sel_side                     none
% 7.74/1.58  --inst_solver_per_active                1400
% 7.74/1.58  --inst_solver_calls_frac                1.
% 7.74/1.58  --inst_passive_queue_type               priority_queues
% 7.74/1.58  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.74/1.58  --inst_passive_queues_freq              [25;2]
% 7.74/1.58  --inst_dismatching                      true
% 7.74/1.58  --inst_eager_unprocessed_to_passive     true
% 7.74/1.58  --inst_prop_sim_given                   true
% 7.74/1.58  --inst_prop_sim_new                     false
% 7.74/1.58  --inst_subs_new                         false
% 7.74/1.58  --inst_eq_res_simp                      false
% 7.74/1.58  --inst_subs_given                       false
% 7.74/1.58  --inst_orphan_elimination               true
% 7.74/1.58  --inst_learning_loop_flag               true
% 7.74/1.58  --inst_learning_start                   3000
% 7.74/1.58  --inst_learning_factor                  2
% 7.74/1.58  --inst_start_prop_sim_after_learn       3
% 7.74/1.58  --inst_sel_renew                        solver
% 7.74/1.58  --inst_lit_activity_flag                true
% 7.74/1.58  --inst_restr_to_given                   false
% 7.74/1.58  --inst_activity_threshold               500
% 7.74/1.58  --inst_out_proof                        true
% 7.74/1.58  
% 7.74/1.58  ------ Resolution Options
% 7.74/1.58  
% 7.74/1.58  --resolution_flag                       false
% 7.74/1.58  --res_lit_sel                           adaptive
% 7.74/1.58  --res_lit_sel_side                      none
% 7.74/1.58  --res_ordering                          kbo
% 7.74/1.58  --res_to_prop_solver                    active
% 7.74/1.58  --res_prop_simpl_new                    false
% 7.74/1.58  --res_prop_simpl_given                  true
% 7.74/1.58  --res_passive_queue_type                priority_queues
% 7.74/1.58  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.74/1.58  --res_passive_queues_freq               [15;5]
% 7.74/1.58  --res_forward_subs                      full
% 7.74/1.58  --res_backward_subs                     full
% 7.74/1.58  --res_forward_subs_resolution           true
% 7.74/1.58  --res_backward_subs_resolution          true
% 7.74/1.58  --res_orphan_elimination                true
% 7.74/1.58  --res_time_limit                        2.
% 7.74/1.58  --res_out_proof                         true
% 7.74/1.58  
% 7.74/1.58  ------ Superposition Options
% 7.74/1.58  
% 7.74/1.58  --superposition_flag                    true
% 7.74/1.58  --sup_passive_queue_type                priority_queues
% 7.74/1.58  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.74/1.58  --sup_passive_queues_freq               [8;1;4]
% 7.74/1.58  --demod_completeness_check              fast
% 7.74/1.58  --demod_use_ground                      true
% 7.74/1.58  --sup_to_prop_solver                    passive
% 7.74/1.58  --sup_prop_simpl_new                    true
% 7.74/1.58  --sup_prop_simpl_given                  true
% 7.74/1.58  --sup_fun_splitting                     true
% 7.74/1.58  --sup_smt_interval                      50000
% 7.74/1.58  
% 7.74/1.58  ------ Superposition Simplification Setup
% 7.74/1.58  
% 7.74/1.58  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.74/1.58  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.74/1.58  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.74/1.58  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.74/1.58  --sup_full_triv                         [TrivRules;PropSubs]
% 7.74/1.58  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.74/1.58  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.74/1.58  --sup_immed_triv                        [TrivRules]
% 7.74/1.58  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.58  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.58  --sup_immed_bw_main                     []
% 7.74/1.58  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.74/1.58  --sup_input_triv                        [Unflattening;TrivRules]
% 7.74/1.58  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.74/1.58  --sup_input_bw                          []
% 7.74/1.58  
% 7.74/1.58  ------ Combination Options
% 7.74/1.58  
% 7.74/1.58  --comb_res_mult                         3
% 7.74/1.58  --comb_sup_mult                         2
% 7.74/1.58  --comb_inst_mult                        10
% 7.74/1.58  
% 7.74/1.58  ------ Debug Options
% 7.74/1.58  
% 7.74/1.58  --dbg_backtrace                         false
% 7.74/1.58  --dbg_dump_prop_clauses                 false
% 7.74/1.58  --dbg_dump_prop_clauses_file            -
% 7.74/1.58  --dbg_out_stat                          false
% 7.74/1.58  
% 7.74/1.58  
% 7.74/1.58  
% 7.74/1.58  
% 7.74/1.58  ------ Proving...
% 7.74/1.58  
% 7.74/1.58  
% 7.74/1.58  % SZS status Theorem for theBenchmark.p
% 7.74/1.58  
% 7.74/1.58   Resolution empty clause
% 7.74/1.58  
% 7.74/1.58  % SZS output start CNFRefutation for theBenchmark.p
% 7.74/1.58  
% 7.74/1.58  fof(f4,axiom,(
% 7.74/1.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f22,plain,(
% 7.74/1.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.74/1.58    inference(ennf_transformation,[],[f4])).
% 7.74/1.58  
% 7.74/1.58  fof(f50,plain,(
% 7.74/1.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f22])).
% 7.74/1.58  
% 7.74/1.58  fof(f8,axiom,(
% 7.74/1.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f26,plain,(
% 7.74/1.58    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 7.74/1.58    inference(ennf_transformation,[],[f8])).
% 7.74/1.58  
% 7.74/1.58  fof(f55,plain,(
% 7.74/1.58    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f26])).
% 7.74/1.58  
% 7.74/1.58  fof(f6,axiom,(
% 7.74/1.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f23,plain,(
% 7.74/1.58    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.74/1.58    inference(ennf_transformation,[],[f6])).
% 7.74/1.58  
% 7.74/1.58  fof(f24,plain,(
% 7.74/1.58    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.74/1.58    inference(flattening,[],[f23])).
% 7.74/1.58  
% 7.74/1.58  fof(f53,plain,(
% 7.74/1.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f24])).
% 7.74/1.58  
% 7.74/1.58  fof(f15,conjecture,(
% 7.74/1.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f16,negated_conjecture,(
% 7.74/1.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 7.74/1.58    inference(negated_conjecture,[],[f15])).
% 7.74/1.58  
% 7.74/1.58  fof(f37,plain,(
% 7.74/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.74/1.58    inference(ennf_transformation,[],[f16])).
% 7.74/1.58  
% 7.74/1.58  fof(f38,plain,(
% 7.74/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.74/1.58    inference(flattening,[],[f37])).
% 7.74/1.58  
% 7.74/1.58  fof(f44,plain,(
% 7.74/1.58    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.74/1.58    introduced(choice_axiom,[])).
% 7.74/1.58  
% 7.74/1.58  fof(f43,plain,(
% 7.74/1.58    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 7.74/1.58    introduced(choice_axiom,[])).
% 7.74/1.58  
% 7.74/1.58  fof(f42,plain,(
% 7.74/1.58    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.74/1.58    introduced(choice_axiom,[])).
% 7.74/1.58  
% 7.74/1.58  fof(f41,plain,(
% 7.74/1.58    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.74/1.58    introduced(choice_axiom,[])).
% 7.74/1.58  
% 7.74/1.58  fof(f40,plain,(
% 7.74/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.74/1.58    introduced(choice_axiom,[])).
% 7.74/1.58  
% 7.74/1.58  fof(f45,plain,(
% 7.74/1.58    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.74/1.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f38,f44,f43,f42,f41,f40])).
% 7.74/1.58  
% 7.74/1.58  fof(f72,plain,(
% 7.74/1.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f9,axiom,(
% 7.74/1.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f17,plain,(
% 7.74/1.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.74/1.58    inference(pure_predicate_removal,[],[f9])).
% 7.74/1.58  
% 7.74/1.58  fof(f27,plain,(
% 7.74/1.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.58    inference(ennf_transformation,[],[f17])).
% 7.74/1.58  
% 7.74/1.58  fof(f56,plain,(
% 7.74/1.58    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.58    inference(cnf_transformation,[],[f27])).
% 7.74/1.58  
% 7.74/1.58  fof(f3,axiom,(
% 7.74/1.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f21,plain,(
% 7.74/1.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.74/1.58    inference(ennf_transformation,[],[f3])).
% 7.74/1.58  
% 7.74/1.58  fof(f39,plain,(
% 7.74/1.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.74/1.58    inference(nnf_transformation,[],[f21])).
% 7.74/1.58  
% 7.74/1.58  fof(f48,plain,(
% 7.74/1.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f39])).
% 7.74/1.58  
% 7.74/1.58  fof(f2,axiom,(
% 7.74/1.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f20,plain,(
% 7.74/1.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.74/1.58    inference(ennf_transformation,[],[f2])).
% 7.74/1.58  
% 7.74/1.58  fof(f47,plain,(
% 7.74/1.58    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f20])).
% 7.74/1.58  
% 7.74/1.58  fof(f5,axiom,(
% 7.74/1.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f51,plain,(
% 7.74/1.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.74/1.58    inference(cnf_transformation,[],[f5])).
% 7.74/1.58  
% 7.74/1.58  fof(f1,axiom,(
% 7.74/1.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f18,plain,(
% 7.74/1.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.74/1.58    inference(ennf_transformation,[],[f1])).
% 7.74/1.58  
% 7.74/1.58  fof(f19,plain,(
% 7.74/1.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.74/1.58    inference(flattening,[],[f18])).
% 7.74/1.58  
% 7.74/1.58  fof(f46,plain,(
% 7.74/1.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f19])).
% 7.74/1.58  
% 7.74/1.58  fof(f7,axiom,(
% 7.74/1.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f25,plain,(
% 7.74/1.58    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.74/1.58    inference(ennf_transformation,[],[f7])).
% 7.74/1.58  
% 7.74/1.58  fof(f54,plain,(
% 7.74/1.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f25])).
% 7.74/1.58  
% 7.74/1.58  fof(f11,axiom,(
% 7.74/1.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f29,plain,(
% 7.74/1.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.74/1.58    inference(ennf_transformation,[],[f11])).
% 7.74/1.58  
% 7.74/1.58  fof(f30,plain,(
% 7.74/1.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.74/1.58    inference(flattening,[],[f29])).
% 7.74/1.58  
% 7.74/1.58  fof(f58,plain,(
% 7.74/1.58    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f30])).
% 7.74/1.58  
% 7.74/1.58  fof(f10,axiom,(
% 7.74/1.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f28,plain,(
% 7.74/1.58    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.74/1.58    inference(ennf_transformation,[],[f10])).
% 7.74/1.58  
% 7.74/1.58  fof(f57,plain,(
% 7.74/1.58    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.74/1.58    inference(cnf_transformation,[],[f28])).
% 7.74/1.58  
% 7.74/1.58  fof(f12,axiom,(
% 7.74/1.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f31,plain,(
% 7.74/1.58    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.74/1.58    inference(ennf_transformation,[],[f12])).
% 7.74/1.58  
% 7.74/1.58  fof(f32,plain,(
% 7.74/1.58    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.74/1.58    inference(flattening,[],[f31])).
% 7.74/1.58  
% 7.74/1.58  fof(f59,plain,(
% 7.74/1.58    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f32])).
% 7.74/1.58  
% 7.74/1.58  fof(f70,plain,(
% 7.74/1.58    v1_funct_1(sK3)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f71,plain,(
% 7.74/1.58    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f14,axiom,(
% 7.74/1.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f35,plain,(
% 7.74/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.74/1.58    inference(ennf_transformation,[],[f14])).
% 7.74/1.58  
% 7.74/1.58  fof(f36,plain,(
% 7.74/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.74/1.58    inference(flattening,[],[f35])).
% 7.74/1.58  
% 7.74/1.58  fof(f61,plain,(
% 7.74/1.58    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f36])).
% 7.74/1.58  
% 7.74/1.58  fof(f69,plain,(
% 7.74/1.58    m1_pre_topc(sK2,sK0)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f62,plain,(
% 7.74/1.58    ~v2_struct_0(sK0)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f63,plain,(
% 7.74/1.58    v2_pre_topc(sK0)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f64,plain,(
% 7.74/1.58    l1_pre_topc(sK0)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f67,plain,(
% 7.74/1.58    l1_pre_topc(sK1)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f65,plain,(
% 7.74/1.58    ~v2_struct_0(sK1)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f66,plain,(
% 7.74/1.58    v2_pre_topc(sK1)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f75,plain,(
% 7.74/1.58    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f74,plain,(
% 7.74/1.58    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 7.74/1.58    inference(cnf_transformation,[],[f45])).
% 7.74/1.58  
% 7.74/1.58  fof(f13,axiom,(
% 7.74/1.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.74/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.74/1.58  
% 7.74/1.58  fof(f33,plain,(
% 7.74/1.58    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.74/1.58    inference(ennf_transformation,[],[f13])).
% 7.74/1.58  
% 7.74/1.58  fof(f34,plain,(
% 7.74/1.58    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.74/1.58    inference(flattening,[],[f33])).
% 7.74/1.58  
% 7.74/1.58  fof(f60,plain,(
% 7.74/1.58    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.74/1.58    inference(cnf_transformation,[],[f34])).
% 7.74/1.58  
% 7.74/1.58  cnf(c_4,plain,
% 7.74/1.58      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.74/1.58      inference(cnf_transformation,[],[f50]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1073,plain,
% 7.74/1.58      ( ~ v1_relat_1(X0_53) | v1_relat_1(k7_relat_1(X0_53,X1_53)) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_4]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1402,plain,
% 7.74/1.58      ( v1_relat_1(X0_53) != iProver_top
% 7.74/1.58      | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1073]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_9,plain,
% 7.74/1.58      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f55]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1068,plain,
% 7.74/1.58      ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) | ~ v1_relat_1(X0_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_9]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1407,plain,
% 7.74/1.58      ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) = iProver_top
% 7.74/1.58      | v1_relat_1(X0_53) != iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1068]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_6,plain,
% 7.74/1.58      ( ~ r1_tarski(X0,X1)
% 7.74/1.58      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.74/1.58      | ~ v1_relat_1(X0)
% 7.74/1.58      | ~ v1_relat_1(X1) ),
% 7.74/1.58      inference(cnf_transformation,[],[f53]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1071,plain,
% 7.74/1.58      ( ~ r1_tarski(X0_53,X1_53)
% 7.74/1.58      | r1_tarski(k2_relat_1(X0_53),k2_relat_1(X1_53))
% 7.74/1.58      | ~ v1_relat_1(X0_53)
% 7.74/1.58      | ~ v1_relat_1(X1_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_6]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1404,plain,
% 7.74/1.58      ( r1_tarski(X0_53,X1_53) != iProver_top
% 7.74/1.58      | r1_tarski(k2_relat_1(X0_53),k2_relat_1(X1_53)) = iProver_top
% 7.74/1.58      | v1_relat_1(X0_53) != iProver_top
% 7.74/1.58      | v1_relat_1(X1_53) != iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1071]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_19,negated_conjecture,
% 7.74/1.58      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.74/1.58      inference(cnf_transformation,[],[f72]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1062,negated_conjecture,
% 7.74/1.58      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_19]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1412,plain,
% 7.74/1.58      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1062]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_10,plain,
% 7.74/1.58      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.74/1.58      inference(cnf_transformation,[],[f56]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_3,plain,
% 7.74/1.58      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f48]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_315,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.58      | r1_tarski(k2_relat_1(X0),X2)
% 7.74/1.58      | ~ v1_relat_1(X0) ),
% 7.74/1.58      inference(resolution,[status(thm)],[c_10,c_3]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1061,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.74/1.58      | r1_tarski(k2_relat_1(X0_53),X2_53)
% 7.74/1.58      | ~ v1_relat_1(X0_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_315]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1413,plain,
% 7.74/1.58      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.74/1.58      | r1_tarski(k2_relat_1(X0_53),X2_53) = iProver_top
% 7.74/1.58      | v1_relat_1(X0_53) != iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1061]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2396,plain,
% 7.74/1.58      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
% 7.74/1.58      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_1412,c_1413]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_40,plain,
% 7.74/1.58      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f47]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1074,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.74/1.58      | ~ v1_relat_1(X1_53)
% 7.74/1.58      | v1_relat_1(X0_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_1]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1445,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0_53))
% 7.74/1.58      | ~ v1_relat_1(X0_53)
% 7.74/1.58      | v1_relat_1(sK3) ),
% 7.74/1.58      inference(instantiation,[status(thm)],[c_1074]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1487,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.74/1.58      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53))
% 7.74/1.58      | v1_relat_1(sK3) ),
% 7.74/1.58      inference(instantiation,[status(thm)],[c_1445]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1624,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.74/1.58      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 7.74/1.58      | v1_relat_1(sK3) ),
% 7.74/1.58      inference(instantiation,[status(thm)],[c_1487]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1625,plain,
% 7.74/1.58      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.58      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 7.74/1.58      | v1_relat_1(sK3) = iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1624]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_5,plain,
% 7.74/1.58      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.74/1.58      inference(cnf_transformation,[],[f51]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1072,plain,
% 7.74/1.58      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_5]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1658,plain,
% 7.74/1.58      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 7.74/1.58      inference(instantiation,[status(thm)],[c_1072]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1659,plain,
% 7.74/1.58      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1658]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1998,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.74/1.58      | r1_tarski(k2_relat_1(sK3),X1_53)
% 7.74/1.58      | ~ v1_relat_1(sK3) ),
% 7.74/1.58      inference(instantiation,[status(thm)],[c_1061]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2346,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.74/1.58      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
% 7.74/1.58      | ~ v1_relat_1(sK3) ),
% 7.74/1.58      inference(instantiation,[status(thm)],[c_1998]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2347,plain,
% 7.74/1.58      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.74/1.58      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top
% 7.74/1.58      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_2346]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2400,plain,
% 7.74/1.58      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 7.74/1.58      inference(global_propositional_subsumption,
% 7.74/1.58                [status(thm)],
% 7.74/1.58                [c_2396,c_40,c_1625,c_1659,c_2347]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_0,plain,
% 7.74/1.58      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.74/1.58      inference(cnf_transformation,[],[f46]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1075,plain,
% 7.74/1.58      ( ~ r1_tarski(X0_53,X1_53)
% 7.74/1.58      | ~ r1_tarski(X2_53,X0_53)
% 7.74/1.58      | r1_tarski(X2_53,X1_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_0]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1400,plain,
% 7.74/1.58      ( r1_tarski(X0_53,X1_53) != iProver_top
% 7.74/1.58      | r1_tarski(X2_53,X0_53) != iProver_top
% 7.74/1.58      | r1_tarski(X2_53,X1_53) = iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1075]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2404,plain,
% 7.74/1.58      ( r1_tarski(X0_53,u1_struct_0(sK1)) = iProver_top
% 7.74/1.58      | r1_tarski(X0_53,k2_relat_1(sK3)) != iProver_top ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_2400,c_1400]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2468,plain,
% 7.74/1.58      ( r1_tarski(X0_53,sK3) != iProver_top
% 7.74/1.58      | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
% 7.74/1.58      | v1_relat_1(X0_53) != iProver_top
% 7.74/1.58      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_1404,c_2404]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2902,plain,
% 7.74/1.58      ( v1_relat_1(X0_53) != iProver_top
% 7.74/1.58      | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
% 7.74/1.58      | r1_tarski(X0_53,sK3) != iProver_top ),
% 7.74/1.58      inference(global_propositional_subsumption,
% 7.74/1.58                [status(thm)],
% 7.74/1.58                [c_2468,c_40,c_1625,c_1659]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2903,plain,
% 7.74/1.58      ( r1_tarski(X0_53,sK3) != iProver_top
% 7.74/1.58      | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK1)) = iProver_top
% 7.74/1.58      | v1_relat_1(X0_53) != iProver_top ),
% 7.74/1.58      inference(renaming,[status(thm)],[c_2902]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_8,plain,
% 7.74/1.58      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f54]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1069,plain,
% 7.74/1.58      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
% 7.74/1.58      | ~ v1_relat_1(X0_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_8]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1406,plain,
% 7.74/1.58      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
% 7.74/1.58      | v1_relat_1(X0_53) != iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1069]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_12,plain,
% 7.74/1.58      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.58      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.74/1.58      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.74/1.58      | ~ v1_relat_1(X0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f58]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1066,plain,
% 7.74/1.58      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.74/1.58      | ~ r1_tarski(k1_relat_1(X0_53),X1_53)
% 7.74/1.58      | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
% 7.74/1.58      | ~ v1_relat_1(X0_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_12]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1409,plain,
% 7.74/1.58      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
% 7.74/1.58      | r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
% 7.74/1.58      | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
% 7.74/1.58      | v1_relat_1(X0_53) != iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1066]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_11,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.58      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 7.74/1.58      inference(cnf_transformation,[],[f57]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1067,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.74/1.58      | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_11]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1408,plain,
% 7.74/1.58      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 7.74/1.58      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2078,plain,
% 7.74/1.58      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 7.74/1.58      | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
% 7.74/1.58      | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
% 7.74/1.58      | v1_relat_1(X2_53) != iProver_top ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_1409,c_1408]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_7342,plain,
% 7.74/1.58      ( k8_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k10_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 7.74/1.58      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 7.74/1.58      | v1_relat_1(X2_53) != iProver_top
% 7.74/1.58      | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_1406,c_2078]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_20441,plain,
% 7.74/1.58      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(X1_53,X0_53),X2_53) = k10_relat_1(k7_relat_1(X1_53,X0_53),X2_53)
% 7.74/1.58      | r1_tarski(k7_relat_1(X1_53,X0_53),sK3) != iProver_top
% 7.74/1.58      | v1_relat_1(X1_53) != iProver_top
% 7.74/1.58      | v1_relat_1(k7_relat_1(X1_53,X0_53)) != iProver_top ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_2903,c_7342]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_21141,plain,
% 7.74/1.58      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
% 7.74/1.58      | v1_relat_1(k7_relat_1(sK3,X0_53)) != iProver_top
% 7.74/1.58      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_1407,c_20441]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_21996,plain,
% 7.74/1.58      ( v1_relat_1(k7_relat_1(sK3,X0_53)) != iProver_top
% 7.74/1.58      | k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
% 7.74/1.58      inference(global_propositional_subsumption,
% 7.74/1.58                [status(thm)],
% 7.74/1.58                [c_21141,c_40,c_1625,c_1659]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_21997,plain,
% 7.74/1.58      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
% 7.74/1.58      | v1_relat_1(k7_relat_1(sK3,X0_53)) != iProver_top ),
% 7.74/1.58      inference(renaming,[status(thm)],[c_21996]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_22002,plain,
% 7.74/1.58      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53)
% 7.74/1.58      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_1402,c_21997]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_22150,plain,
% 7.74/1.58      ( k8_relset_1(X0_53,u1_struct_0(sK1),k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
% 7.74/1.58      inference(global_propositional_subsumption,
% 7.74/1.58                [status(thm)],
% 7.74/1.58                [c_22002,c_40,c_1625,c_1659]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_2010,plain,
% 7.74/1.58      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_1412,c_1408]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_13,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.58      | ~ v1_funct_1(X0)
% 7.74/1.58      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.74/1.58      inference(cnf_transformation,[],[f59]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_21,negated_conjecture,
% 7.74/1.58      ( v1_funct_1(sK3) ),
% 7.74/1.58      inference(cnf_transformation,[],[f70]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_427,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.74/1.58      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 7.74/1.58      | sK3 != X0 ),
% 7.74/1.58      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_428,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.74/1.58      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.74/1.58      inference(unflattening,[status(thm)],[c_427]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1059,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.74/1.58      | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_428]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1415,plain,
% 7.74/1.58      ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
% 7.74/1.58      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 7.74/1.58      inference(predicate_to_equality,[status(thm)],[c_1059]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1570,plain,
% 7.74/1.58      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
% 7.74/1.58      inference(superposition,[status(thm)],[c_1412,c_1415]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_20,negated_conjecture,
% 7.74/1.58      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.74/1.58      inference(cnf_transformation,[],[f71]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_15,plain,
% 7.74/1.58      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.74/1.58      | ~ m1_pre_topc(X3,X1)
% 7.74/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.74/1.58      | v2_struct_0(X1)
% 7.74/1.58      | v2_struct_0(X2)
% 7.74/1.58      | ~ v2_pre_topc(X2)
% 7.74/1.58      | ~ v2_pre_topc(X1)
% 7.74/1.58      | ~ l1_pre_topc(X2)
% 7.74/1.58      | ~ l1_pre_topc(X1)
% 7.74/1.58      | ~ v1_funct_1(X0)
% 7.74/1.58      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.74/1.58      inference(cnf_transformation,[],[f61]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_22,negated_conjecture,
% 7.74/1.58      ( m1_pre_topc(sK2,sK0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f69]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_334,plain,
% 7.74/1.58      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.74/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.74/1.58      | v2_struct_0(X2)
% 7.74/1.58      | v2_struct_0(X1)
% 7.74/1.58      | ~ v2_pre_topc(X2)
% 7.74/1.58      | ~ v2_pre_topc(X1)
% 7.74/1.58      | ~ l1_pre_topc(X2)
% 7.74/1.58      | ~ l1_pre_topc(X1)
% 7.74/1.58      | ~ v1_funct_1(X0)
% 7.74/1.58      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 7.74/1.58      | sK2 != X3
% 7.74/1.58      | sK0 != X1 ),
% 7.74/1.58      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_335,plain,
% 7.74/1.58      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.74/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.74/1.58      | v2_struct_0(X1)
% 7.74/1.58      | v2_struct_0(sK0)
% 7.74/1.58      | ~ v2_pre_topc(X1)
% 7.74/1.58      | ~ v2_pre_topc(sK0)
% 7.74/1.58      | ~ l1_pre_topc(X1)
% 7.74/1.58      | ~ l1_pre_topc(sK0)
% 7.74/1.58      | ~ v1_funct_1(X0)
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 7.74/1.58      inference(unflattening,[status(thm)],[c_334]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_29,negated_conjecture,
% 7.74/1.58      ( ~ v2_struct_0(sK0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f62]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_28,negated_conjecture,
% 7.74/1.58      ( v2_pre_topc(sK0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f63]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_27,negated_conjecture,
% 7.74/1.58      ( l1_pre_topc(sK0) ),
% 7.74/1.58      inference(cnf_transformation,[],[f64]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_339,plain,
% 7.74/1.58      ( ~ l1_pre_topc(X1)
% 7.74/1.58      | v2_struct_0(X1)
% 7.74/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.74/1.58      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.74/1.58      | ~ v2_pre_topc(X1)
% 7.74/1.58      | ~ v1_funct_1(X0)
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 7.74/1.58      inference(global_propositional_subsumption,
% 7.74/1.58                [status(thm)],
% 7.74/1.58                [c_335,c_29,c_28,c_27]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_340,plain,
% 7.74/1.58      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 7.74/1.58      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.74/1.58      | v2_struct_0(X1)
% 7.74/1.58      | ~ v2_pre_topc(X1)
% 7.74/1.58      | ~ l1_pre_topc(X1)
% 7.74/1.58      | ~ v1_funct_1(X0)
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 7.74/1.58      inference(renaming,[status(thm)],[c_339]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_375,plain,
% 7.74/1.58      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 7.74/1.58      | v2_struct_0(X1)
% 7.74/1.58      | ~ v2_pre_topc(X1)
% 7.74/1.58      | ~ l1_pre_topc(X1)
% 7.74/1.58      | ~ v1_funct_1(X0)
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
% 7.74/1.58      | u1_struct_0(X1) != u1_struct_0(sK1)
% 7.74/1.58      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.74/1.58      | sK3 != X0 ),
% 7.74/1.58      inference(resolution_lifted,[status(thm)],[c_20,c_340]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_376,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 7.74/1.58      | v2_struct_0(X0)
% 7.74/1.58      | ~ v2_pre_topc(X0)
% 7.74/1.58      | ~ l1_pre_topc(X0)
% 7.74/1.58      | ~ v1_funct_1(sK3)
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 7.74/1.58      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 7.74/1.58      inference(unflattening,[status(thm)],[c_375]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_380,plain,
% 7.74/1.58      ( ~ l1_pre_topc(X0)
% 7.74/1.58      | ~ v2_pre_topc(X0)
% 7.74/1.58      | v2_struct_0(X0)
% 7.74/1.58      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 7.74/1.58      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 7.74/1.58      inference(global_propositional_subsumption,[status(thm)],[c_376,c_21]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_381,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 7.74/1.58      | v2_struct_0(X0)
% 7.74/1.58      | ~ v2_pre_topc(X0)
% 7.74/1.58      | ~ l1_pre_topc(X0)
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 7.74/1.58      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 7.74/1.58      inference(renaming,[status(thm)],[c_380]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_24,negated_conjecture,
% 7.74/1.58      ( l1_pre_topc(sK1) ),
% 7.74/1.58      inference(cnf_transformation,[],[f67]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_446,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 7.74/1.58      | v2_struct_0(X0)
% 7.74/1.58      | ~ v2_pre_topc(X0)
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 7.74/1.58      | u1_struct_0(X0) != u1_struct_0(sK1)
% 7.74/1.58      | sK1 != X0 ),
% 7.74/1.58      inference(resolution_lifted,[status(thm)],[c_381,c_24]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_447,plain,
% 7.74/1.58      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.74/1.58      | v2_struct_0(sK1)
% 7.74/1.58      | ~ v2_pre_topc(sK1)
% 7.74/1.58      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 7.74/1.58      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 7.74/1.58      inference(unflattening,[status(thm)],[c_446]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_26,negated_conjecture,
% 7.74/1.58      ( ~ v2_struct_0(sK1) ),
% 7.74/1.58      inference(cnf_transformation,[],[f65]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_25,negated_conjecture,
% 7.74/1.58      ( v2_pre_topc(sK1) ),
% 7.74/1.58      inference(cnf_transformation,[],[f66]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_449,plain,
% 7.74/1.58      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 7.74/1.58      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 7.74/1.58      inference(global_propositional_subsumption,
% 7.74/1.58                [status(thm)],
% 7.74/1.58                [c_447,c_26,c_25,c_19]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_734,plain,
% 7.74/1.58      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 7.74/1.58      inference(equality_resolution_simp,[status(thm)],[c_449]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1057,plain,
% 7.74/1.58      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 7.74/1.58      inference(subtyping,[status(esa)],[c_734]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_1618,plain,
% 7.74/1.58      ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 7.74/1.58      inference(demodulation,[status(thm)],[c_1570,c_1057]) ).
% 7.74/1.58  
% 7.74/1.58  cnf(c_16,negated_conjecture,
% 7.74/1.58      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 7.74/1.59      inference(cnf_transformation,[],[f75]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_1065,negated_conjecture,
% 7.74/1.59      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 7.74/1.59      inference(subtyping,[status(esa)],[c_16]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_1794,plain,
% 7.74/1.59      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
% 7.74/1.59      inference(demodulation,[status(thm)],[c_1618,c_1065]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_2151,plain,
% 7.74/1.59      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 7.74/1.59      inference(demodulation,[status(thm)],[c_2010,c_1794]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_22153,plain,
% 7.74/1.59      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 7.74/1.59      inference(demodulation,[status(thm)],[c_22150,c_2151]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_17,negated_conjecture,
% 7.74/1.59      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 7.74/1.59      inference(cnf_transformation,[],[f74]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_1064,negated_conjecture,
% 7.74/1.59      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 7.74/1.59      inference(subtyping,[status(esa)],[c_17]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_1410,plain,
% 7.74/1.59      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 7.74/1.59      inference(predicate_to_equality,[status(thm)],[c_1064]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_2153,plain,
% 7.74/1.59      ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 7.74/1.59      inference(demodulation,[status(thm)],[c_2010,c_1410]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_14,plain,
% 7.74/1.59      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 7.74/1.59      | ~ v1_funct_1(X0)
% 7.74/1.59      | ~ v1_relat_1(X0)
% 7.74/1.59      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
% 7.74/1.59      inference(cnf_transformation,[],[f60]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_412,plain,
% 7.74/1.59      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 7.74/1.59      | ~ v1_relat_1(X0)
% 7.74/1.59      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
% 7.74/1.59      | sK3 != X0 ),
% 7.74/1.59      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_413,plain,
% 7.74/1.59      ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
% 7.74/1.59      | ~ v1_relat_1(sK3)
% 7.74/1.59      | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
% 7.74/1.59      inference(unflattening,[status(thm)],[c_412]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_1060,plain,
% 7.74/1.59      ( ~ r1_tarski(k10_relat_1(sK3,X0_53),X1_53)
% 7.74/1.59      | ~ v1_relat_1(sK3)
% 7.74/1.59      | k10_relat_1(k7_relat_1(sK3,X1_53),X0_53) = k10_relat_1(sK3,X0_53) ),
% 7.74/1.59      inference(subtyping,[status(esa)],[c_413]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_1414,plain,
% 7.74/1.59      ( k10_relat_1(k7_relat_1(sK3,X0_53),X1_53) = k10_relat_1(sK3,X1_53)
% 7.74/1.59      | r1_tarski(k10_relat_1(sK3,X1_53),X0_53) != iProver_top
% 7.74/1.59      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.59      inference(predicate_to_equality,[status(thm)],[c_1060]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_2254,plain,
% 7.74/1.59      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4)
% 7.74/1.59      | v1_relat_1(sK3) != iProver_top ),
% 7.74/1.59      inference(superposition,[status(thm)],[c_2153,c_1414]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_2359,plain,
% 7.74/1.59      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
% 7.74/1.59      inference(global_propositional_subsumption,
% 7.74/1.59                [status(thm)],
% 7.74/1.59                [c_2254,c_40,c_1625,c_1659]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_22154,plain,
% 7.74/1.59      ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
% 7.74/1.59      inference(light_normalisation,[status(thm)],[c_22153,c_2359]) ).
% 7.74/1.59  
% 7.74/1.59  cnf(c_22155,plain,
% 7.74/1.59      ( $false ),
% 7.74/1.59      inference(equality_resolution_simp,[status(thm)],[c_22154]) ).
% 7.74/1.59  
% 7.74/1.59  
% 7.74/1.59  % SZS output end CNFRefutation for theBenchmark.p
% 7.74/1.59  
% 7.74/1.59  ------                               Statistics
% 7.74/1.59  
% 7.74/1.59  ------ General
% 7.74/1.59  
% 7.74/1.59  abstr_ref_over_cycles:                  0
% 7.74/1.59  abstr_ref_under_cycles:                 0
% 7.74/1.59  gc_basic_clause_elim:                   0
% 7.74/1.59  forced_gc_time:                         0
% 7.74/1.59  parsing_time:                           0.01
% 7.74/1.59  unif_index_cands_time:                  0.
% 7.74/1.59  unif_index_add_time:                    0.
% 7.74/1.59  orderings_time:                         0.
% 7.74/1.59  out_proof_time:                         0.012
% 7.74/1.59  total_time:                             0.81
% 7.74/1.59  num_of_symbols:                         59
% 7.74/1.59  num_of_terms:                           36360
% 7.74/1.59  
% 7.74/1.59  ------ Preprocessing
% 7.74/1.59  
% 7.74/1.59  num_of_splits:                          0
% 7.74/1.59  num_of_split_atoms:                     0
% 7.74/1.59  num_of_reused_defs:                     0
% 7.74/1.59  num_eq_ax_congr_red:                    17
% 7.74/1.59  num_of_sem_filtered_clauses:            1
% 7.74/1.59  num_of_subtypes:                        3
% 7.74/1.59  monotx_restored_types:                  0
% 7.74/1.59  sat_num_of_epr_types:                   0
% 7.74/1.59  sat_num_of_non_cyclic_types:            0
% 7.74/1.59  sat_guarded_non_collapsed_types:        0
% 7.74/1.59  num_pure_diseq_elim:                    0
% 7.74/1.59  simp_replaced_by:                       0
% 7.74/1.59  res_preprocessed:                       116
% 7.74/1.59  prep_upred:                             0
% 7.74/1.59  prep_unflattend:                        25
% 7.74/1.59  smt_new_axioms:                         0
% 7.74/1.59  pred_elim_cands:                        3
% 7.74/1.59  pred_elim:                              7
% 7.74/1.59  pred_elim_cl:                           11
% 7.74/1.59  pred_elim_cycles:                       9
% 7.74/1.59  merged_defs:                            0
% 7.74/1.59  merged_defs_ncl:                        0
% 7.74/1.59  bin_hyper_res:                          0
% 7.74/1.59  prep_cycles:                            4
% 7.74/1.59  pred_elim_time:                         0.015
% 7.74/1.59  splitting_time:                         0.
% 7.74/1.59  sem_filter_time:                        0.
% 7.74/1.59  monotx_time:                            0.
% 7.74/1.59  subtype_inf_time:                       0.
% 7.74/1.59  
% 7.74/1.59  ------ Problem properties
% 7.74/1.59  
% 7.74/1.59  clauses:                                19
% 7.74/1.59  conjectures:                            4
% 7.74/1.59  epr:                                    1
% 7.74/1.59  horn:                                   19
% 7.74/1.59  ground:                                 6
% 7.74/1.59  unary:                                  6
% 7.74/1.59  binary:                                 5
% 7.74/1.59  lits:                                   43
% 7.74/1.59  lits_eq:                                7
% 7.74/1.59  fd_pure:                                0
% 7.74/1.59  fd_pseudo:                              0
% 7.74/1.59  fd_cond:                                0
% 7.74/1.59  fd_pseudo_cond:                         0
% 7.74/1.59  ac_symbols:                             0
% 7.74/1.59  
% 7.74/1.59  ------ Propositional Solver
% 7.74/1.59  
% 7.74/1.59  prop_solver_calls:                      36
% 7.74/1.59  prop_fast_solver_calls:                 1606
% 7.74/1.59  smt_solver_calls:                       0
% 7.74/1.59  smt_fast_solver_calls:                  0
% 7.74/1.59  prop_num_of_clauses:                    10954
% 7.74/1.59  prop_preprocess_simplified:             13508
% 7.74/1.59  prop_fo_subsumed:                       32
% 7.74/1.59  prop_solver_time:                       0.
% 7.74/1.59  smt_solver_time:                        0.
% 7.74/1.59  smt_fast_solver_time:                   0.
% 7.74/1.59  prop_fast_solver_time:                  0.
% 7.74/1.59  prop_unsat_core_time:                   0.
% 7.74/1.59  
% 7.74/1.59  ------ QBF
% 7.74/1.59  
% 7.74/1.59  qbf_q_res:                              0
% 7.74/1.59  qbf_num_tautologies:                    0
% 7.74/1.59  qbf_prep_cycles:                        0
% 7.74/1.59  
% 7.74/1.59  ------ BMC1
% 7.74/1.59  
% 7.74/1.59  bmc1_current_bound:                     -1
% 7.74/1.59  bmc1_last_solved_bound:                 -1
% 7.74/1.59  bmc1_unsat_core_size:                   -1
% 7.74/1.59  bmc1_unsat_core_parents_size:           -1
% 7.74/1.59  bmc1_merge_next_fun:                    0
% 7.74/1.59  bmc1_unsat_core_clauses_time:           0.
% 7.74/1.59  
% 7.74/1.59  ------ Instantiation
% 7.74/1.59  
% 7.74/1.59  inst_num_of_clauses:                    1960
% 7.74/1.59  inst_num_in_passive:                    508
% 7.74/1.59  inst_num_in_active:                     1096
% 7.74/1.59  inst_num_in_unprocessed:                356
% 7.74/1.59  inst_num_of_loops:                      1160
% 7.74/1.59  inst_num_of_learning_restarts:          0
% 7.74/1.59  inst_num_moves_active_passive:          56
% 7.74/1.59  inst_lit_activity:                      0
% 7.74/1.59  inst_lit_activity_moves:                0
% 7.74/1.59  inst_num_tautologies:                   0
% 7.74/1.59  inst_num_prop_implied:                  0
% 7.74/1.59  inst_num_existing_simplified:           0
% 7.74/1.59  inst_num_eq_res_simplified:             0
% 7.74/1.59  inst_num_child_elim:                    0
% 7.74/1.59  inst_num_of_dismatching_blockings:      2134
% 7.74/1.59  inst_num_of_non_proper_insts:           3181
% 7.74/1.59  inst_num_of_duplicates:                 0
% 7.74/1.59  inst_inst_num_from_inst_to_res:         0
% 7.74/1.59  inst_dismatching_checking_time:         0.
% 7.74/1.59  
% 7.74/1.59  ------ Resolution
% 7.74/1.59  
% 7.74/1.59  res_num_of_clauses:                     0
% 7.74/1.59  res_num_in_passive:                     0
% 7.74/1.59  res_num_in_active:                      0
% 7.74/1.59  res_num_of_loops:                       120
% 7.74/1.59  res_forward_subset_subsumed:            237
% 7.74/1.59  res_backward_subset_subsumed:           0
% 7.74/1.59  res_forward_subsumed:                   0
% 7.74/1.59  res_backward_subsumed:                  0
% 7.74/1.59  res_forward_subsumption_resolution:     0
% 7.74/1.59  res_backward_subsumption_resolution:    0
% 7.74/1.59  res_clause_to_clause_subsumption:       8589
% 7.74/1.59  res_orphan_elimination:                 0
% 7.74/1.59  res_tautology_del:                      577
% 7.74/1.59  res_num_eq_res_simplified:              1
% 7.74/1.59  res_num_sel_changes:                    0
% 7.74/1.59  res_moves_from_active_to_pass:          0
% 7.74/1.59  
% 7.74/1.59  ------ Superposition
% 7.74/1.59  
% 7.74/1.59  sup_time_total:                         0.
% 7.74/1.59  sup_time_generating:                    0.
% 7.74/1.59  sup_time_sim_full:                      0.
% 7.74/1.59  sup_time_sim_immed:                     0.
% 7.74/1.59  
% 7.74/1.59  sup_num_of_clauses:                     1416
% 7.74/1.59  sup_num_in_active:                      208
% 7.74/1.59  sup_num_in_passive:                     1208
% 7.74/1.59  sup_num_of_loops:                       230
% 7.74/1.59  sup_fw_superposition:                   916
% 7.74/1.59  sup_bw_superposition:                   644
% 7.74/1.59  sup_immediate_simplified:               19
% 7.74/1.59  sup_given_eliminated:                   0
% 7.74/1.59  comparisons_done:                       0
% 7.74/1.59  comparisons_avoided:                    0
% 7.74/1.59  
% 7.74/1.59  ------ Simplifications
% 7.74/1.59  
% 7.74/1.59  
% 7.74/1.59  sim_fw_subset_subsumed:                 4
% 7.74/1.59  sim_bw_subset_subsumed:                 50
% 7.74/1.59  sim_fw_subsumed:                        13
% 7.74/1.59  sim_bw_subsumed:                        1
% 7.74/1.59  sim_fw_subsumption_res:                 0
% 7.74/1.59  sim_bw_subsumption_res:                 0
% 7.74/1.59  sim_tautology_del:                      2
% 7.74/1.59  sim_eq_tautology_del:                   0
% 7.74/1.59  sim_eq_res_simp:                        0
% 7.74/1.59  sim_fw_demodulated:                     5
% 7.74/1.59  sim_bw_demodulated:                     10
% 7.74/1.59  sim_light_normalised:                   1
% 7.74/1.59  sim_joinable_taut:                      0
% 7.74/1.59  sim_joinable_simp:                      0
% 7.74/1.59  sim_ac_normalised:                      0
% 7.74/1.59  sim_smt_subsumption:                    0
% 7.74/1.59  
%------------------------------------------------------------------------------
