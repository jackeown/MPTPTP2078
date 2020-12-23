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
% DateTime   : Thu Dec  3 12:22:34 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 390 expanded)
%              Number of clauses        :   84 ( 108 expanded)
%              Number of leaves         :   20 ( 139 expanded)
%              Depth                    :   24
%              Number of atoms          :  535 (3533 expanded)
%              Number of equality atoms :  134 ( 439 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4)
        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f36,f42,f41,f40,f39,f38])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
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

fof(f66,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f71,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1284,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1277,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_308,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_9])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_308])).

cnf(c_1276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_1490,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1276])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1288,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1962,plain,
    ( r1_tarski(X0,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_1288])).

cnf(c_2179,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1962])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1357,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1418,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1357])).

cnf(c_1419,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1418])).

cnf(c_2269,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2179,c_39,c_1419])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1285,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1280,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1281,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1954,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1281])).

cnf(c_11064,plain,
    ( k8_relset_1(X0,X1,k7_relat_1(X2,X0),X3) = k10_relat_1(k7_relat_1(X2,X0),X3)
    | r1_tarski(k2_relat_1(k7_relat_1(X2,X0)),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k7_relat_1(X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1954])).

cnf(c_29680,plain,
    ( k8_relset_1(X0,u1_struct_0(sK1),k7_relat_1(sK3,X0),X1) = k10_relat_1(k7_relat_1(sK3,X0),X1)
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_11064])).

cnf(c_1282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1605,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1282])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1283,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1875,plain,
    ( k10_relat_1(k7_relat_1(sK3,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_1605,c_1283])).

cnf(c_29693,plain,
    ( k8_relset_1(X0,u1_struct_0(sK1),k7_relat_1(sK3,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK3,X1))
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29680,c_1875])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1997,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1998,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1997])).

cnf(c_29852,plain,
    ( k8_relset_1(X0,u1_struct_0(sK1),k7_relat_1(sK3,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29693,c_39,c_1419,c_1998])).

cnf(c_1955,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1277,c_1281])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_403,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_1275,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_1405,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1277,c_1275])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f68])).

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
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_324,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_325,plain,
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
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_329,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_28,c_27,c_26])).

cnf(c_330,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_330])).

cnf(c_366,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_370,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_20])).

cnf(c_371,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_417,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_371,c_23])).

cnf(c_418,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_420,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_25,c_24,c_18])).

cnf(c_686,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_420])).

cnf(c_1459,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_1405,c_686])).

cnf(c_15,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1693,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1459,c_15])).

cnf(c_2014,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1955,c_1693])).

cnf(c_29855,plain,
    ( k3_xboole_0(u1_struct_0(sK2),k10_relat_1(sK3,sK4)) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_29852,c_2014])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1279,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1287,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1563,plain,
    ( k3_xboole_0(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1279,c_1287])).

cnf(c_1654,plain,
    ( k3_xboole_0(u1_struct_0(sK2),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(superposition,[status(thm)],[c_0,c_1563])).

cnf(c_2013,plain,
    ( k3_xboole_0(u1_struct_0(sK2),k10_relat_1(sK3,sK4)) = k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1955,c_1654])).

cnf(c_29856,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_29855,c_2013])).

cnf(c_29857,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_29856])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.00/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.00/1.48  
% 8.00/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.00/1.48  
% 8.00/1.48  ------  iProver source info
% 8.00/1.48  
% 8.00/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.00/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.00/1.48  git: non_committed_changes: false
% 8.00/1.48  git: last_make_outside_of_git: false
% 8.00/1.48  
% 8.00/1.48  ------ 
% 8.00/1.48  
% 8.00/1.48  ------ Input Options
% 8.00/1.48  
% 8.00/1.48  --out_options                           all
% 8.00/1.48  --tptp_safe_out                         true
% 8.00/1.48  --problem_path                          ""
% 8.00/1.48  --include_path                          ""
% 8.00/1.48  --clausifier                            res/vclausify_rel
% 8.00/1.48  --clausifier_options                    ""
% 8.00/1.48  --stdin                                 false
% 8.00/1.48  --stats_out                             all
% 8.00/1.48  
% 8.00/1.48  ------ General Options
% 8.00/1.48  
% 8.00/1.48  --fof                                   false
% 8.00/1.48  --time_out_real                         305.
% 8.00/1.48  --time_out_virtual                      -1.
% 8.00/1.48  --symbol_type_check                     false
% 8.00/1.48  --clausify_out                          false
% 8.00/1.48  --sig_cnt_out                           false
% 8.00/1.48  --trig_cnt_out                          false
% 8.00/1.48  --trig_cnt_out_tolerance                1.
% 8.00/1.48  --trig_cnt_out_sk_spl                   false
% 8.00/1.48  --abstr_cl_out                          false
% 8.00/1.48  
% 8.00/1.48  ------ Global Options
% 8.00/1.48  
% 8.00/1.48  --schedule                              default
% 8.00/1.48  --add_important_lit                     false
% 8.00/1.48  --prop_solver_per_cl                    1000
% 8.00/1.48  --min_unsat_core                        false
% 8.00/1.48  --soft_assumptions                      false
% 8.00/1.48  --soft_lemma_size                       3
% 8.00/1.48  --prop_impl_unit_size                   0
% 8.00/1.48  --prop_impl_unit                        []
% 8.00/1.48  --share_sel_clauses                     true
% 8.00/1.48  --reset_solvers                         false
% 8.00/1.48  --bc_imp_inh                            [conj_cone]
% 8.00/1.48  --conj_cone_tolerance                   3.
% 8.00/1.48  --extra_neg_conj                        none
% 8.00/1.48  --large_theory_mode                     true
% 8.00/1.48  --prolific_symb_bound                   200
% 8.00/1.48  --lt_threshold                          2000
% 8.00/1.48  --clause_weak_htbl                      true
% 8.00/1.48  --gc_record_bc_elim                     false
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing Options
% 8.00/1.48  
% 8.00/1.48  --preprocessing_flag                    true
% 8.00/1.48  --time_out_prep_mult                    0.1
% 8.00/1.48  --splitting_mode                        input
% 8.00/1.48  --splitting_grd                         true
% 8.00/1.48  --splitting_cvd                         false
% 8.00/1.48  --splitting_cvd_svl                     false
% 8.00/1.48  --splitting_nvd                         32
% 8.00/1.48  --sub_typing                            true
% 8.00/1.48  --prep_gs_sim                           true
% 8.00/1.48  --prep_unflatten                        true
% 8.00/1.48  --prep_res_sim                          true
% 8.00/1.48  --prep_upred                            true
% 8.00/1.48  --prep_sem_filter                       exhaustive
% 8.00/1.48  --prep_sem_filter_out                   false
% 8.00/1.48  --pred_elim                             true
% 8.00/1.48  --res_sim_input                         true
% 8.00/1.48  --eq_ax_congr_red                       true
% 8.00/1.48  --pure_diseq_elim                       true
% 8.00/1.48  --brand_transform                       false
% 8.00/1.48  --non_eq_to_eq                          false
% 8.00/1.48  --prep_def_merge                        true
% 8.00/1.48  --prep_def_merge_prop_impl              false
% 8.00/1.48  --prep_def_merge_mbd                    true
% 8.00/1.48  --prep_def_merge_tr_red                 false
% 8.00/1.48  --prep_def_merge_tr_cl                  false
% 8.00/1.48  --smt_preprocessing                     true
% 8.00/1.48  --smt_ac_axioms                         fast
% 8.00/1.48  --preprocessed_out                      false
% 8.00/1.48  --preprocessed_stats                    false
% 8.00/1.48  
% 8.00/1.48  ------ Abstraction refinement Options
% 8.00/1.48  
% 8.00/1.48  --abstr_ref                             []
% 8.00/1.48  --abstr_ref_prep                        false
% 8.00/1.48  --abstr_ref_until_sat                   false
% 8.00/1.48  --abstr_ref_sig_restrict                funpre
% 8.00/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.48  --abstr_ref_under                       []
% 8.00/1.48  
% 8.00/1.48  ------ SAT Options
% 8.00/1.48  
% 8.00/1.48  --sat_mode                              false
% 8.00/1.48  --sat_fm_restart_options                ""
% 8.00/1.48  --sat_gr_def                            false
% 8.00/1.48  --sat_epr_types                         true
% 8.00/1.48  --sat_non_cyclic_types                  false
% 8.00/1.48  --sat_finite_models                     false
% 8.00/1.48  --sat_fm_lemmas                         false
% 8.00/1.48  --sat_fm_prep                           false
% 8.00/1.48  --sat_fm_uc_incr                        true
% 8.00/1.48  --sat_out_model                         small
% 8.00/1.48  --sat_out_clauses                       false
% 8.00/1.48  
% 8.00/1.48  ------ QBF Options
% 8.00/1.48  
% 8.00/1.48  --qbf_mode                              false
% 8.00/1.48  --qbf_elim_univ                         false
% 8.00/1.48  --qbf_dom_inst                          none
% 8.00/1.48  --qbf_dom_pre_inst                      false
% 8.00/1.48  --qbf_sk_in                             false
% 8.00/1.48  --qbf_pred_elim                         true
% 8.00/1.48  --qbf_split                             512
% 8.00/1.48  
% 8.00/1.48  ------ BMC1 Options
% 8.00/1.48  
% 8.00/1.48  --bmc1_incremental                      false
% 8.00/1.48  --bmc1_axioms                           reachable_all
% 8.00/1.48  --bmc1_min_bound                        0
% 8.00/1.48  --bmc1_max_bound                        -1
% 8.00/1.48  --bmc1_max_bound_default                -1
% 8.00/1.48  --bmc1_symbol_reachability              true
% 8.00/1.48  --bmc1_property_lemmas                  false
% 8.00/1.48  --bmc1_k_induction                      false
% 8.00/1.48  --bmc1_non_equiv_states                 false
% 8.00/1.48  --bmc1_deadlock                         false
% 8.00/1.48  --bmc1_ucm                              false
% 8.00/1.48  --bmc1_add_unsat_core                   none
% 8.00/1.48  --bmc1_unsat_core_children              false
% 8.00/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.48  --bmc1_out_stat                         full
% 8.00/1.48  --bmc1_ground_init                      false
% 8.00/1.48  --bmc1_pre_inst_next_state              false
% 8.00/1.48  --bmc1_pre_inst_state                   false
% 8.00/1.48  --bmc1_pre_inst_reach_state             false
% 8.00/1.48  --bmc1_out_unsat_core                   false
% 8.00/1.48  --bmc1_aig_witness_out                  false
% 8.00/1.48  --bmc1_verbose                          false
% 8.00/1.48  --bmc1_dump_clauses_tptp                false
% 8.00/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.48  --bmc1_dump_file                        -
% 8.00/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.48  --bmc1_ucm_extend_mode                  1
% 8.00/1.48  --bmc1_ucm_init_mode                    2
% 8.00/1.48  --bmc1_ucm_cone_mode                    none
% 8.00/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.48  --bmc1_ucm_relax_model                  4
% 8.00/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.48  --bmc1_ucm_layered_model                none
% 8.00/1.48  --bmc1_ucm_max_lemma_size               10
% 8.00/1.48  
% 8.00/1.48  ------ AIG Options
% 8.00/1.48  
% 8.00/1.48  --aig_mode                              false
% 8.00/1.48  
% 8.00/1.48  ------ Instantiation Options
% 8.00/1.48  
% 8.00/1.48  --instantiation_flag                    true
% 8.00/1.48  --inst_sos_flag                         true
% 8.00/1.48  --inst_sos_phase                        true
% 8.00/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.48  --inst_lit_sel_side                     num_symb
% 8.00/1.48  --inst_solver_per_active                1400
% 8.00/1.48  --inst_solver_calls_frac                1.
% 8.00/1.48  --inst_passive_queue_type               priority_queues
% 8.00/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.48  --inst_passive_queues_freq              [25;2]
% 8.00/1.48  --inst_dismatching                      true
% 8.00/1.48  --inst_eager_unprocessed_to_passive     true
% 8.00/1.48  --inst_prop_sim_given                   true
% 8.00/1.48  --inst_prop_sim_new                     false
% 8.00/1.48  --inst_subs_new                         false
% 8.00/1.48  --inst_eq_res_simp                      false
% 8.00/1.48  --inst_subs_given                       false
% 8.00/1.48  --inst_orphan_elimination               true
% 8.00/1.48  --inst_learning_loop_flag               true
% 8.00/1.48  --inst_learning_start                   3000
% 8.00/1.48  --inst_learning_factor                  2
% 8.00/1.48  --inst_start_prop_sim_after_learn       3
% 8.00/1.48  --inst_sel_renew                        solver
% 8.00/1.48  --inst_lit_activity_flag                true
% 8.00/1.48  --inst_restr_to_given                   false
% 8.00/1.48  --inst_activity_threshold               500
% 8.00/1.48  --inst_out_proof                        true
% 8.00/1.48  
% 8.00/1.48  ------ Resolution Options
% 8.00/1.48  
% 8.00/1.48  --resolution_flag                       true
% 8.00/1.48  --res_lit_sel                           adaptive
% 8.00/1.48  --res_lit_sel_side                      none
% 8.00/1.48  --res_ordering                          kbo
% 8.00/1.48  --res_to_prop_solver                    active
% 8.00/1.48  --res_prop_simpl_new                    false
% 8.00/1.48  --res_prop_simpl_given                  true
% 8.00/1.48  --res_passive_queue_type                priority_queues
% 8.00/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.48  --res_passive_queues_freq               [15;5]
% 8.00/1.48  --res_forward_subs                      full
% 8.00/1.48  --res_backward_subs                     full
% 8.00/1.48  --res_forward_subs_resolution           true
% 8.00/1.48  --res_backward_subs_resolution          true
% 8.00/1.48  --res_orphan_elimination                true
% 8.00/1.48  --res_time_limit                        2.
% 8.00/1.48  --res_out_proof                         true
% 8.00/1.48  
% 8.00/1.48  ------ Superposition Options
% 8.00/1.48  
% 8.00/1.48  --superposition_flag                    true
% 8.00/1.48  --sup_passive_queue_type                priority_queues
% 8.00/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.48  --demod_completeness_check              fast
% 8.00/1.48  --demod_use_ground                      true
% 8.00/1.48  --sup_to_prop_solver                    passive
% 8.00/1.48  --sup_prop_simpl_new                    true
% 8.00/1.48  --sup_prop_simpl_given                  true
% 8.00/1.48  --sup_fun_splitting                     true
% 8.00/1.48  --sup_smt_interval                      50000
% 8.00/1.48  
% 8.00/1.48  ------ Superposition Simplification Setup
% 8.00/1.48  
% 8.00/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.00/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.00/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.00/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.00/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.00/1.48  --sup_immed_triv                        [TrivRules]
% 8.00/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_immed_bw_main                     []
% 8.00/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.00/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_input_bw                          []
% 8.00/1.48  
% 8.00/1.48  ------ Combination Options
% 8.00/1.48  
% 8.00/1.48  --comb_res_mult                         3
% 8.00/1.48  --comb_sup_mult                         2
% 8.00/1.48  --comb_inst_mult                        10
% 8.00/1.48  
% 8.00/1.48  ------ Debug Options
% 8.00/1.48  
% 8.00/1.48  --dbg_backtrace                         false
% 8.00/1.48  --dbg_dump_prop_clauses                 false
% 8.00/1.48  --dbg_dump_prop_clauses_file            -
% 8.00/1.48  --dbg_out_stat                          false
% 8.00/1.48  ------ Parsing...
% 8.00/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.00/1.48  ------ Proving...
% 8.00/1.48  ------ Problem Properties 
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  clauses                                 18
% 8.00/1.48  conjectures                             4
% 8.00/1.48  EPR                                     1
% 8.00/1.48  Horn                                    18
% 8.00/1.48  unary                                   6
% 8.00/1.48  binary                                  9
% 8.00/1.48  lits                                    34
% 8.00/1.48  lits eq                                 9
% 8.00/1.48  fd_pure                                 0
% 8.00/1.48  fd_pseudo                               0
% 8.00/1.48  fd_cond                                 0
% 8.00/1.48  fd_pseudo_cond                          0
% 8.00/1.48  AC symbols                              0
% 8.00/1.48  
% 8.00/1.48  ------ Schedule dynamic 5 is on 
% 8.00/1.48  
% 8.00/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  ------ 
% 8.00/1.48  Current options:
% 8.00/1.48  ------ 
% 8.00/1.48  
% 8.00/1.48  ------ Input Options
% 8.00/1.48  
% 8.00/1.48  --out_options                           all
% 8.00/1.48  --tptp_safe_out                         true
% 8.00/1.48  --problem_path                          ""
% 8.00/1.48  --include_path                          ""
% 8.00/1.48  --clausifier                            res/vclausify_rel
% 8.00/1.48  --clausifier_options                    ""
% 8.00/1.48  --stdin                                 false
% 8.00/1.48  --stats_out                             all
% 8.00/1.48  
% 8.00/1.48  ------ General Options
% 8.00/1.48  
% 8.00/1.48  --fof                                   false
% 8.00/1.48  --time_out_real                         305.
% 8.00/1.48  --time_out_virtual                      -1.
% 8.00/1.48  --symbol_type_check                     false
% 8.00/1.48  --clausify_out                          false
% 8.00/1.48  --sig_cnt_out                           false
% 8.00/1.48  --trig_cnt_out                          false
% 8.00/1.48  --trig_cnt_out_tolerance                1.
% 8.00/1.48  --trig_cnt_out_sk_spl                   false
% 8.00/1.48  --abstr_cl_out                          false
% 8.00/1.48  
% 8.00/1.48  ------ Global Options
% 8.00/1.48  
% 8.00/1.48  --schedule                              default
% 8.00/1.48  --add_important_lit                     false
% 8.00/1.48  --prop_solver_per_cl                    1000
% 8.00/1.48  --min_unsat_core                        false
% 8.00/1.48  --soft_assumptions                      false
% 8.00/1.48  --soft_lemma_size                       3
% 8.00/1.48  --prop_impl_unit_size                   0
% 8.00/1.48  --prop_impl_unit                        []
% 8.00/1.48  --share_sel_clauses                     true
% 8.00/1.48  --reset_solvers                         false
% 8.00/1.48  --bc_imp_inh                            [conj_cone]
% 8.00/1.48  --conj_cone_tolerance                   3.
% 8.00/1.48  --extra_neg_conj                        none
% 8.00/1.48  --large_theory_mode                     true
% 8.00/1.48  --prolific_symb_bound                   200
% 8.00/1.48  --lt_threshold                          2000
% 8.00/1.48  --clause_weak_htbl                      true
% 8.00/1.48  --gc_record_bc_elim                     false
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing Options
% 8.00/1.48  
% 8.00/1.48  --preprocessing_flag                    true
% 8.00/1.48  --time_out_prep_mult                    0.1
% 8.00/1.48  --splitting_mode                        input
% 8.00/1.48  --splitting_grd                         true
% 8.00/1.48  --splitting_cvd                         false
% 8.00/1.48  --splitting_cvd_svl                     false
% 8.00/1.48  --splitting_nvd                         32
% 8.00/1.48  --sub_typing                            true
% 8.00/1.48  --prep_gs_sim                           true
% 8.00/1.48  --prep_unflatten                        true
% 8.00/1.48  --prep_res_sim                          true
% 8.00/1.48  --prep_upred                            true
% 8.00/1.48  --prep_sem_filter                       exhaustive
% 8.00/1.48  --prep_sem_filter_out                   false
% 8.00/1.48  --pred_elim                             true
% 8.00/1.48  --res_sim_input                         true
% 8.00/1.48  --eq_ax_congr_red                       true
% 8.00/1.48  --pure_diseq_elim                       true
% 8.00/1.48  --brand_transform                       false
% 8.00/1.48  --non_eq_to_eq                          false
% 8.00/1.48  --prep_def_merge                        true
% 8.00/1.48  --prep_def_merge_prop_impl              false
% 8.00/1.48  --prep_def_merge_mbd                    true
% 8.00/1.48  --prep_def_merge_tr_red                 false
% 8.00/1.48  --prep_def_merge_tr_cl                  false
% 8.00/1.48  --smt_preprocessing                     true
% 8.00/1.48  --smt_ac_axioms                         fast
% 8.00/1.48  --preprocessed_out                      false
% 8.00/1.48  --preprocessed_stats                    false
% 8.00/1.48  
% 8.00/1.48  ------ Abstraction refinement Options
% 8.00/1.48  
% 8.00/1.48  --abstr_ref                             []
% 8.00/1.48  --abstr_ref_prep                        false
% 8.00/1.48  --abstr_ref_until_sat                   false
% 8.00/1.48  --abstr_ref_sig_restrict                funpre
% 8.00/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.48  --abstr_ref_under                       []
% 8.00/1.48  
% 8.00/1.48  ------ SAT Options
% 8.00/1.48  
% 8.00/1.48  --sat_mode                              false
% 8.00/1.48  --sat_fm_restart_options                ""
% 8.00/1.48  --sat_gr_def                            false
% 8.00/1.48  --sat_epr_types                         true
% 8.00/1.48  --sat_non_cyclic_types                  false
% 8.00/1.48  --sat_finite_models                     false
% 8.00/1.48  --sat_fm_lemmas                         false
% 8.00/1.48  --sat_fm_prep                           false
% 8.00/1.48  --sat_fm_uc_incr                        true
% 8.00/1.48  --sat_out_model                         small
% 8.00/1.48  --sat_out_clauses                       false
% 8.00/1.48  
% 8.00/1.48  ------ QBF Options
% 8.00/1.48  
% 8.00/1.48  --qbf_mode                              false
% 8.00/1.48  --qbf_elim_univ                         false
% 8.00/1.48  --qbf_dom_inst                          none
% 8.00/1.48  --qbf_dom_pre_inst                      false
% 8.00/1.48  --qbf_sk_in                             false
% 8.00/1.48  --qbf_pred_elim                         true
% 8.00/1.48  --qbf_split                             512
% 8.00/1.48  
% 8.00/1.48  ------ BMC1 Options
% 8.00/1.48  
% 8.00/1.48  --bmc1_incremental                      false
% 8.00/1.48  --bmc1_axioms                           reachable_all
% 8.00/1.48  --bmc1_min_bound                        0
% 8.00/1.48  --bmc1_max_bound                        -1
% 8.00/1.48  --bmc1_max_bound_default                -1
% 8.00/1.48  --bmc1_symbol_reachability              true
% 8.00/1.48  --bmc1_property_lemmas                  false
% 8.00/1.48  --bmc1_k_induction                      false
% 8.00/1.48  --bmc1_non_equiv_states                 false
% 8.00/1.48  --bmc1_deadlock                         false
% 8.00/1.48  --bmc1_ucm                              false
% 8.00/1.48  --bmc1_add_unsat_core                   none
% 8.00/1.48  --bmc1_unsat_core_children              false
% 8.00/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.48  --bmc1_out_stat                         full
% 8.00/1.48  --bmc1_ground_init                      false
% 8.00/1.48  --bmc1_pre_inst_next_state              false
% 8.00/1.48  --bmc1_pre_inst_state                   false
% 8.00/1.48  --bmc1_pre_inst_reach_state             false
% 8.00/1.48  --bmc1_out_unsat_core                   false
% 8.00/1.48  --bmc1_aig_witness_out                  false
% 8.00/1.48  --bmc1_verbose                          false
% 8.00/1.48  --bmc1_dump_clauses_tptp                false
% 8.00/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.48  --bmc1_dump_file                        -
% 8.00/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.48  --bmc1_ucm_extend_mode                  1
% 8.00/1.48  --bmc1_ucm_init_mode                    2
% 8.00/1.48  --bmc1_ucm_cone_mode                    none
% 8.00/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.48  --bmc1_ucm_relax_model                  4
% 8.00/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.48  --bmc1_ucm_layered_model                none
% 8.00/1.48  --bmc1_ucm_max_lemma_size               10
% 8.00/1.48  
% 8.00/1.48  ------ AIG Options
% 8.00/1.48  
% 8.00/1.48  --aig_mode                              false
% 8.00/1.48  
% 8.00/1.48  ------ Instantiation Options
% 8.00/1.48  
% 8.00/1.48  --instantiation_flag                    true
% 8.00/1.48  --inst_sos_flag                         true
% 8.00/1.48  --inst_sos_phase                        true
% 8.00/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.48  --inst_lit_sel_side                     none
% 8.00/1.48  --inst_solver_per_active                1400
% 8.00/1.48  --inst_solver_calls_frac                1.
% 8.00/1.48  --inst_passive_queue_type               priority_queues
% 8.00/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.48  --inst_passive_queues_freq              [25;2]
% 8.00/1.48  --inst_dismatching                      true
% 8.00/1.48  --inst_eager_unprocessed_to_passive     true
% 8.00/1.48  --inst_prop_sim_given                   true
% 8.00/1.48  --inst_prop_sim_new                     false
% 8.00/1.48  --inst_subs_new                         false
% 8.00/1.48  --inst_eq_res_simp                      false
% 8.00/1.48  --inst_subs_given                       false
% 8.00/1.48  --inst_orphan_elimination               true
% 8.00/1.48  --inst_learning_loop_flag               true
% 8.00/1.48  --inst_learning_start                   3000
% 8.00/1.48  --inst_learning_factor                  2
% 8.00/1.48  --inst_start_prop_sim_after_learn       3
% 8.00/1.48  --inst_sel_renew                        solver
% 8.00/1.48  --inst_lit_activity_flag                true
% 8.00/1.48  --inst_restr_to_given                   false
% 8.00/1.48  --inst_activity_threshold               500
% 8.00/1.48  --inst_out_proof                        true
% 8.00/1.48  
% 8.00/1.48  ------ Resolution Options
% 8.00/1.48  
% 8.00/1.48  --resolution_flag                       false
% 8.00/1.48  --res_lit_sel                           adaptive
% 8.00/1.48  --res_lit_sel_side                      none
% 8.00/1.48  --res_ordering                          kbo
% 8.00/1.48  --res_to_prop_solver                    active
% 8.00/1.48  --res_prop_simpl_new                    false
% 8.00/1.48  --res_prop_simpl_given                  true
% 8.00/1.48  --res_passive_queue_type                priority_queues
% 8.00/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.48  --res_passive_queues_freq               [15;5]
% 8.00/1.48  --res_forward_subs                      full
% 8.00/1.48  --res_backward_subs                     full
% 8.00/1.48  --res_forward_subs_resolution           true
% 8.00/1.48  --res_backward_subs_resolution          true
% 8.00/1.48  --res_orphan_elimination                true
% 8.00/1.48  --res_time_limit                        2.
% 8.00/1.48  --res_out_proof                         true
% 8.00/1.48  
% 8.00/1.48  ------ Superposition Options
% 8.00/1.48  
% 8.00/1.48  --superposition_flag                    true
% 8.00/1.48  --sup_passive_queue_type                priority_queues
% 8.00/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.48  --demod_completeness_check              fast
% 8.00/1.48  --demod_use_ground                      true
% 8.00/1.48  --sup_to_prop_solver                    passive
% 8.00/1.48  --sup_prop_simpl_new                    true
% 8.00/1.48  --sup_prop_simpl_given                  true
% 8.00/1.48  --sup_fun_splitting                     true
% 8.00/1.48  --sup_smt_interval                      50000
% 8.00/1.48  
% 8.00/1.48  ------ Superposition Simplification Setup
% 8.00/1.48  
% 8.00/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.00/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.00/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.00/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.00/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.00/1.48  --sup_immed_triv                        [TrivRules]
% 8.00/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_immed_bw_main                     []
% 8.00/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.00/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_input_bw                          []
% 8.00/1.48  
% 8.00/1.48  ------ Combination Options
% 8.00/1.48  
% 8.00/1.48  --comb_res_mult                         3
% 8.00/1.48  --comb_sup_mult                         2
% 8.00/1.48  --comb_inst_mult                        10
% 8.00/1.48  
% 8.00/1.48  ------ Debug Options
% 8.00/1.48  
% 8.00/1.48  --dbg_backtrace                         false
% 8.00/1.48  --dbg_dump_prop_clauses                 false
% 8.00/1.48  --dbg_dump_prop_clauses_file            -
% 8.00/1.48  --dbg_out_stat                          false
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  ------ Proving...
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  % SZS status Theorem for theBenchmark.p
% 8.00/1.48  
% 8.00/1.48   Resolution empty clause
% 8.00/1.48  
% 8.00/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.00/1.48  
% 8.00/1.48  fof(f7,axiom,(
% 8.00/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f24,plain,(
% 8.00/1.48    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 8.00/1.48    inference(ennf_transformation,[],[f7])).
% 8.00/1.48  
% 8.00/1.48  fof(f51,plain,(
% 8.00/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f24])).
% 8.00/1.48  
% 8.00/1.48  fof(f15,conjecture,(
% 8.00/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f16,negated_conjecture,(
% 8.00/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 8.00/1.48    inference(negated_conjecture,[],[f15])).
% 8.00/1.48  
% 8.00/1.48  fof(f35,plain,(
% 8.00/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 8.00/1.48    inference(ennf_transformation,[],[f16])).
% 8.00/1.48  
% 8.00/1.48  fof(f36,plain,(
% 8.00/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.00/1.48    inference(flattening,[],[f35])).
% 8.00/1.48  
% 8.00/1.48  fof(f42,plain,(
% 8.00/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 8.00/1.48    introduced(choice_axiom,[])).
% 8.00/1.48  
% 8.00/1.48  fof(f41,plain,(
% 8.00/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 8.00/1.48    introduced(choice_axiom,[])).
% 8.00/1.48  
% 8.00/1.48  fof(f40,plain,(
% 8.00/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 8.00/1.48    introduced(choice_axiom,[])).
% 8.00/1.48  
% 8.00/1.48  fof(f39,plain,(
% 8.00/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 8.00/1.48    introduced(choice_axiom,[])).
% 8.00/1.48  
% 8.00/1.48  fof(f38,plain,(
% 8.00/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 8.00/1.48    introduced(choice_axiom,[])).
% 8.00/1.48  
% 8.00/1.48  fof(f43,plain,(
% 8.00/1.48    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 8.00/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f36,f42,f41,f40,f39,f38])).
% 8.00/1.48  
% 8.00/1.48  fof(f69,plain,(
% 8.00/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f4,axiom,(
% 8.00/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f21,plain,(
% 8.00/1.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.00/1.48    inference(ennf_transformation,[],[f4])).
% 8.00/1.48  
% 8.00/1.48  fof(f37,plain,(
% 8.00/1.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 8.00/1.48    inference(nnf_transformation,[],[f21])).
% 8.00/1.48  
% 8.00/1.48  fof(f47,plain,(
% 8.00/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f37])).
% 8.00/1.48  
% 8.00/1.48  fof(f10,axiom,(
% 8.00/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f17,plain,(
% 8.00/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 8.00/1.48    inference(pure_predicate_removal,[],[f10])).
% 8.00/1.48  
% 8.00/1.48  fof(f27,plain,(
% 8.00/1.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.48    inference(ennf_transformation,[],[f17])).
% 8.00/1.48  
% 8.00/1.48  fof(f54,plain,(
% 8.00/1.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.48    inference(cnf_transformation,[],[f27])).
% 8.00/1.48  
% 8.00/1.48  fof(f9,axiom,(
% 8.00/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f26,plain,(
% 8.00/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.48    inference(ennf_transformation,[],[f9])).
% 8.00/1.48  
% 8.00/1.48  fof(f53,plain,(
% 8.00/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.48    inference(cnf_transformation,[],[f26])).
% 8.00/1.48  
% 8.00/1.48  fof(f2,axiom,(
% 8.00/1.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f18,plain,(
% 8.00/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 8.00/1.48    inference(ennf_transformation,[],[f2])).
% 8.00/1.48  
% 8.00/1.48  fof(f19,plain,(
% 8.00/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 8.00/1.48    inference(flattening,[],[f18])).
% 8.00/1.48  
% 8.00/1.48  fof(f45,plain,(
% 8.00/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f19])).
% 8.00/1.48  
% 8.00/1.48  fof(f6,axiom,(
% 8.00/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f23,plain,(
% 8.00/1.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 8.00/1.48    inference(ennf_transformation,[],[f6])).
% 8.00/1.48  
% 8.00/1.48  fof(f50,plain,(
% 8.00/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f23])).
% 8.00/1.48  
% 8.00/1.48  fof(f12,axiom,(
% 8.00/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f29,plain,(
% 8.00/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 8.00/1.48    inference(ennf_transformation,[],[f12])).
% 8.00/1.48  
% 8.00/1.48  fof(f30,plain,(
% 8.00/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 8.00/1.48    inference(flattening,[],[f29])).
% 8.00/1.48  
% 8.00/1.48  fof(f56,plain,(
% 8.00/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f30])).
% 8.00/1.48  
% 8.00/1.48  fof(f11,axiom,(
% 8.00/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f28,plain,(
% 8.00/1.48    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.48    inference(ennf_transformation,[],[f11])).
% 8.00/1.48  
% 8.00/1.48  fof(f55,plain,(
% 8.00/1.48    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.48    inference(cnf_transformation,[],[f28])).
% 8.00/1.48  
% 8.00/1.48  fof(f8,axiom,(
% 8.00/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f25,plain,(
% 8.00/1.48    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 8.00/1.48    inference(ennf_transformation,[],[f8])).
% 8.00/1.48  
% 8.00/1.48  fof(f52,plain,(
% 8.00/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f25])).
% 8.00/1.48  
% 8.00/1.48  fof(f5,axiom,(
% 8.00/1.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f22,plain,(
% 8.00/1.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 8.00/1.48    inference(ennf_transformation,[],[f5])).
% 8.00/1.48  
% 8.00/1.48  fof(f49,plain,(
% 8.00/1.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f22])).
% 8.00/1.48  
% 8.00/1.48  fof(f13,axiom,(
% 8.00/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f31,plain,(
% 8.00/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 8.00/1.48    inference(ennf_transformation,[],[f13])).
% 8.00/1.48  
% 8.00/1.48  fof(f32,plain,(
% 8.00/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 8.00/1.48    inference(flattening,[],[f31])).
% 8.00/1.48  
% 8.00/1.48  fof(f57,plain,(
% 8.00/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f32])).
% 8.00/1.48  
% 8.00/1.48  fof(f67,plain,(
% 8.00/1.48    v1_funct_1(sK3)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f68,plain,(
% 8.00/1.48    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f14,axiom,(
% 8.00/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f33,plain,(
% 8.00/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.00/1.48    inference(ennf_transformation,[],[f14])).
% 8.00/1.48  
% 8.00/1.48  fof(f34,plain,(
% 8.00/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.00/1.48    inference(flattening,[],[f33])).
% 8.00/1.48  
% 8.00/1.48  fof(f58,plain,(
% 8.00/1.48    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f34])).
% 8.00/1.48  
% 8.00/1.48  fof(f66,plain,(
% 8.00/1.48    m1_pre_topc(sK2,sK0)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f59,plain,(
% 8.00/1.48    ~v2_struct_0(sK0)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f60,plain,(
% 8.00/1.48    v2_pre_topc(sK0)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f61,plain,(
% 8.00/1.48    l1_pre_topc(sK0)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f64,plain,(
% 8.00/1.48    l1_pre_topc(sK1)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f62,plain,(
% 8.00/1.48    ~v2_struct_0(sK1)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f63,plain,(
% 8.00/1.48    v2_pre_topc(sK1)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f72,plain,(
% 8.00/1.48    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f1,axiom,(
% 8.00/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f44,plain,(
% 8.00/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f1])).
% 8.00/1.48  
% 8.00/1.48  fof(f71,plain,(
% 8.00/1.48    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 8.00/1.48    inference(cnf_transformation,[],[f43])).
% 8.00/1.48  
% 8.00/1.48  fof(f3,axiom,(
% 8.00/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 8.00/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f20,plain,(
% 8.00/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 8.00/1.48    inference(ennf_transformation,[],[f3])).
% 8.00/1.48  
% 8.00/1.48  fof(f46,plain,(
% 8.00/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f20])).
% 8.00/1.48  
% 8.00/1.48  cnf(c_7,plain,
% 8.00/1.48      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 8.00/1.48      | ~ v1_relat_1(X0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f51]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1284,plain,
% 8.00/1.48      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) = iProver_top
% 8.00/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_18,negated_conjecture,
% 8.00/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 8.00/1.48      inference(cnf_transformation,[],[f69]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1277,plain,
% 8.00/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_4,plain,
% 8.00/1.48      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f47]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_10,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 8.00/1.48      inference(cnf_transformation,[],[f54]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_303,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.48      | r1_tarski(k2_relat_1(X3),X4)
% 8.00/1.48      | ~ v1_relat_1(X3)
% 8.00/1.48      | X0 != X3
% 8.00/1.48      | X2 != X4 ),
% 8.00/1.48      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_304,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.48      | r1_tarski(k2_relat_1(X0),X2)
% 8.00/1.48      | ~ v1_relat_1(X0) ),
% 8.00/1.48      inference(unflattening,[status(thm)],[c_303]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_9,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f53]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_308,plain,
% 8.00/1.48      ( r1_tarski(k2_relat_1(X0),X2)
% 8.00/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 8.00/1.48      inference(global_propositional_subsumption,[status(thm)],[c_304,c_9]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_309,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.48      | r1_tarski(k2_relat_1(X0),X2) ),
% 8.00/1.48      inference(renaming,[status(thm)],[c_308]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1276,plain,
% 8.00/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.00/1.48      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1490,plain,
% 8.00/1.48      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1277,c_1276]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1,plain,
% 8.00/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 8.00/1.48      inference(cnf_transformation,[],[f45]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1288,plain,
% 8.00/1.48      ( r1_tarski(X0,X1) != iProver_top
% 8.00/1.48      | r1_tarski(X2,X0) != iProver_top
% 8.00/1.48      | r1_tarski(X2,X1) = iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1962,plain,
% 8.00/1.48      ( r1_tarski(X0,u1_struct_0(sK1)) = iProver_top
% 8.00/1.48      | r1_tarski(X0,k2_relat_1(sK3)) != iProver_top ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1490,c_1288]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_2179,plain,
% 8.00/1.48      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK1)) = iProver_top
% 8.00/1.48      | v1_relat_1(sK3) != iProver_top ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1284,c_1962]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_39,plain,
% 8.00/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1357,plain,
% 8.00/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK3) ),
% 8.00/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1418,plain,
% 8.00/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 8.00/1.48      | v1_relat_1(sK3) ),
% 8.00/1.48      inference(instantiation,[status(thm)],[c_1357]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1419,plain,
% 8.00/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 8.00/1.48      | v1_relat_1(sK3) = iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_1418]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_2269,plain,
% 8.00/1.48      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK1)) = iProver_top ),
% 8.00/1.48      inference(global_propositional_subsumption,
% 8.00/1.48                [status(thm)],
% 8.00/1.48                [c_2179,c_39,c_1419]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_6,plain,
% 8.00/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f50]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1285,plain,
% 8.00/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 8.00/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_12,plain,
% 8.00/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.48      | ~ r1_tarski(k1_relat_1(X0),X1)
% 8.00/1.48      | ~ r1_tarski(k2_relat_1(X0),X2)
% 8.00/1.48      | ~ v1_relat_1(X0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f56]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1280,plain,
% 8.00/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 8.00/1.48      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 8.00/1.48      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 8.00/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_11,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.48      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 8.00/1.48      inference(cnf_transformation,[],[f55]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1281,plain,
% 8.00/1.48      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 8.00/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1954,plain,
% 8.00/1.48      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 8.00/1.48      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 8.00/1.48      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 8.00/1.48      | v1_relat_1(X2) != iProver_top ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1280,c_1281]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_11064,plain,
% 8.00/1.48      ( k8_relset_1(X0,X1,k7_relat_1(X2,X0),X3) = k10_relat_1(k7_relat_1(X2,X0),X3)
% 8.00/1.48      | r1_tarski(k2_relat_1(k7_relat_1(X2,X0)),X1) != iProver_top
% 8.00/1.48      | v1_relat_1(X2) != iProver_top
% 8.00/1.48      | v1_relat_1(k7_relat_1(X2,X0)) != iProver_top ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1285,c_1954]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_29680,plain,
% 8.00/1.48      ( k8_relset_1(X0,u1_struct_0(sK1),k7_relat_1(sK3,X0),X1) = k10_relat_1(k7_relat_1(sK3,X0),X1)
% 8.00/1.48      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top
% 8.00/1.48      | v1_relat_1(sK3) != iProver_top ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_2269,c_11064]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1282,plain,
% 8.00/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.00/1.48      | v1_relat_1(X0) = iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1605,plain,
% 8.00/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1277,c_1282]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_8,plain,
% 8.00/1.48      ( ~ v1_relat_1(X0)
% 8.00/1.48      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 8.00/1.48      inference(cnf_transformation,[],[f52]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1283,plain,
% 8.00/1.48      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 8.00/1.48      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1875,plain,
% 8.00/1.48      ( k10_relat_1(k7_relat_1(sK3,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK3,X1)) ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1605,c_1283]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_29693,plain,
% 8.00/1.48      ( k8_relset_1(X0,u1_struct_0(sK1),k7_relat_1(sK3,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK3,X1))
% 8.00/1.48      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top
% 8.00/1.48      | v1_relat_1(sK3) != iProver_top ),
% 8.00/1.48      inference(light_normalisation,[status(thm)],[c_29680,c_1875]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_5,plain,
% 8.00/1.48      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 8.00/1.48      inference(cnf_transformation,[],[f49]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1997,plain,
% 8.00/1.48      ( v1_relat_1(k7_relat_1(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 8.00/1.48      inference(instantiation,[status(thm)],[c_5]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1998,plain,
% 8.00/1.48      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 8.00/1.48      | v1_relat_1(sK3) != iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_1997]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_29852,plain,
% 8.00/1.48      ( k8_relset_1(X0,u1_struct_0(sK1),k7_relat_1(sK3,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK3,X1)) ),
% 8.00/1.48      inference(global_propositional_subsumption,
% 8.00/1.48                [status(thm)],
% 8.00/1.48                [c_29693,c_39,c_1419,c_1998]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1955,plain,
% 8.00/1.48      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k10_relat_1(sK3,X0) ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1277,c_1281]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_13,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.48      | ~ v1_funct_1(X0)
% 8.00/1.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 8.00/1.48      inference(cnf_transformation,[],[f57]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_20,negated_conjecture,
% 8.00/1.48      ( v1_funct_1(sK3) ),
% 8.00/1.48      inference(cnf_transformation,[],[f67]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_402,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 8.00/1.48      | sK3 != X0 ),
% 8.00/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_403,plain,
% 8.00/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.00/1.48      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 8.00/1.48      inference(unflattening,[status(thm)],[c_402]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1275,plain,
% 8.00/1.48      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 8.00/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1405,plain,
% 8.00/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k7_relat_1(sK3,X0) ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1277,c_1275]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_19,negated_conjecture,
% 8.00/1.48      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 8.00/1.48      inference(cnf_transformation,[],[f68]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_14,plain,
% 8.00/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.00/1.48      | ~ m1_pre_topc(X3,X1)
% 8.00/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.00/1.48      | v2_struct_0(X1)
% 8.00/1.48      | v2_struct_0(X2)
% 8.00/1.48      | ~ v2_pre_topc(X2)
% 8.00/1.48      | ~ v2_pre_topc(X1)
% 8.00/1.48      | ~ l1_pre_topc(X2)
% 8.00/1.48      | ~ l1_pre_topc(X1)
% 8.00/1.48      | ~ v1_funct_1(X0)
% 8.00/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 8.00/1.48      inference(cnf_transformation,[],[f58]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_21,negated_conjecture,
% 8.00/1.48      ( m1_pre_topc(sK2,sK0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f66]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_324,plain,
% 8.00/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.00/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.00/1.48      | v2_struct_0(X1)
% 8.00/1.48      | v2_struct_0(X2)
% 8.00/1.48      | ~ v2_pre_topc(X1)
% 8.00/1.48      | ~ v2_pre_topc(X2)
% 8.00/1.48      | ~ l1_pre_topc(X1)
% 8.00/1.48      | ~ l1_pre_topc(X2)
% 8.00/1.48      | ~ v1_funct_1(X0)
% 8.00/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 8.00/1.48      | sK2 != X3
% 8.00/1.48      | sK0 != X1 ),
% 8.00/1.48      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_325,plain,
% 8.00/1.48      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 8.00/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 8.00/1.48      | v2_struct_0(X1)
% 8.00/1.48      | v2_struct_0(sK0)
% 8.00/1.48      | ~ v2_pre_topc(X1)
% 8.00/1.48      | ~ v2_pre_topc(sK0)
% 8.00/1.48      | ~ l1_pre_topc(X1)
% 8.00/1.48      | ~ l1_pre_topc(sK0)
% 8.00/1.48      | ~ v1_funct_1(X0)
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 8.00/1.48      inference(unflattening,[status(thm)],[c_324]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_28,negated_conjecture,
% 8.00/1.48      ( ~ v2_struct_0(sK0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f59]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_27,negated_conjecture,
% 8.00/1.48      ( v2_pre_topc(sK0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f60]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_26,negated_conjecture,
% 8.00/1.48      ( l1_pre_topc(sK0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f61]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_329,plain,
% 8.00/1.48      ( ~ l1_pre_topc(X1)
% 8.00/1.48      | v2_struct_0(X1)
% 8.00/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 8.00/1.48      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 8.00/1.48      | ~ v2_pre_topc(X1)
% 8.00/1.48      | ~ v1_funct_1(X0)
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 8.00/1.48      inference(global_propositional_subsumption,
% 8.00/1.48                [status(thm)],
% 8.00/1.48                [c_325,c_28,c_27,c_26]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_330,plain,
% 8.00/1.48      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 8.00/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 8.00/1.48      | v2_struct_0(X1)
% 8.00/1.48      | ~ v2_pre_topc(X1)
% 8.00/1.48      | ~ l1_pre_topc(X1)
% 8.00/1.48      | ~ v1_funct_1(X0)
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 8.00/1.48      inference(renaming,[status(thm)],[c_329]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_365,plain,
% 8.00/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 8.00/1.48      | v2_struct_0(X1)
% 8.00/1.48      | ~ v2_pre_topc(X1)
% 8.00/1.48      | ~ l1_pre_topc(X1)
% 8.00/1.48      | ~ v1_funct_1(X0)
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
% 8.00/1.48      | u1_struct_0(X1) != u1_struct_0(sK1)
% 8.00/1.48      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 8.00/1.48      | sK3 != X0 ),
% 8.00/1.48      inference(resolution_lifted,[status(thm)],[c_19,c_330]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_366,plain,
% 8.00/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 8.00/1.48      | v2_struct_0(X0)
% 8.00/1.48      | ~ v2_pre_topc(X0)
% 8.00/1.48      | ~ l1_pre_topc(X0)
% 8.00/1.48      | ~ v1_funct_1(sK3)
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 8.00/1.48      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 8.00/1.48      inference(unflattening,[status(thm)],[c_365]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_370,plain,
% 8.00/1.48      ( ~ l1_pre_topc(X0)
% 8.00/1.48      | ~ v2_pre_topc(X0)
% 8.00/1.48      | v2_struct_0(X0)
% 8.00/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 8.00/1.48      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 8.00/1.48      inference(global_propositional_subsumption,[status(thm)],[c_366,c_20]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_371,plain,
% 8.00/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 8.00/1.48      | v2_struct_0(X0)
% 8.00/1.48      | ~ v2_pre_topc(X0)
% 8.00/1.48      | ~ l1_pre_topc(X0)
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 8.00/1.48      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 8.00/1.48      inference(renaming,[status(thm)],[c_370]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_23,negated_conjecture,
% 8.00/1.48      ( l1_pre_topc(sK1) ),
% 8.00/1.48      inference(cnf_transformation,[],[f64]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_417,plain,
% 8.00/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 8.00/1.48      | v2_struct_0(X0)
% 8.00/1.48      | ~ v2_pre_topc(X0)
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 8.00/1.48      | u1_struct_0(X0) != u1_struct_0(sK1)
% 8.00/1.48      | sK1 != X0 ),
% 8.00/1.48      inference(resolution_lifted,[status(thm)],[c_371,c_23]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_418,plain,
% 8.00/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 8.00/1.48      | v2_struct_0(sK1)
% 8.00/1.48      | ~ v2_pre_topc(sK1)
% 8.00/1.48      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 8.00/1.48      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 8.00/1.48      inference(unflattening,[status(thm)],[c_417]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_25,negated_conjecture,
% 8.00/1.48      ( ~ v2_struct_0(sK1) ),
% 8.00/1.48      inference(cnf_transformation,[],[f62]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_24,negated_conjecture,
% 8.00/1.48      ( v2_pre_topc(sK1) ),
% 8.00/1.48      inference(cnf_transformation,[],[f63]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_420,plain,
% 8.00/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 8.00/1.48      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 8.00/1.48      inference(global_propositional_subsumption,
% 8.00/1.48                [status(thm)],
% 8.00/1.48                [c_418,c_25,c_24,c_18]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_686,plain,
% 8.00/1.48      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 8.00/1.48      inference(equality_resolution_simp,[status(thm)],[c_420]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1459,plain,
% 8.00/1.48      ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 8.00/1.48      inference(demodulation,[status(thm)],[c_1405,c_686]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_15,negated_conjecture,
% 8.00/1.48      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 8.00/1.48      inference(cnf_transformation,[],[f72]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1693,plain,
% 8.00/1.48      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
% 8.00/1.48      inference(demodulation,[status(thm)],[c_1459,c_15]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_2014,plain,
% 8.00/1.48      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 8.00/1.48      inference(demodulation,[status(thm)],[c_1955,c_1693]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_29855,plain,
% 8.00/1.48      ( k3_xboole_0(u1_struct_0(sK2),k10_relat_1(sK3,sK4)) != k10_relat_1(sK3,sK4) ),
% 8.00/1.48      inference(demodulation,[status(thm)],[c_29852,c_2014]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_0,plain,
% 8.00/1.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 8.00/1.48      inference(cnf_transformation,[],[f44]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_16,negated_conjecture,
% 8.00/1.48      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 8.00/1.48      inference(cnf_transformation,[],[f71]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1279,plain,
% 8.00/1.48      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_2,plain,
% 8.00/1.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 8.00/1.48      inference(cnf_transformation,[],[f46]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1287,plain,
% 8.00/1.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 8.00/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1563,plain,
% 8.00/1.48      ( k3_xboole_0(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_1279,c_1287]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_1654,plain,
% 8.00/1.48      ( k3_xboole_0(u1_struct_0(sK2),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
% 8.00/1.48      inference(superposition,[status(thm)],[c_0,c_1563]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_2013,plain,
% 8.00/1.48      ( k3_xboole_0(u1_struct_0(sK2),k10_relat_1(sK3,sK4)) = k10_relat_1(sK3,sK4) ),
% 8.00/1.48      inference(demodulation,[status(thm)],[c_1955,c_1654]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_29856,plain,
% 8.00/1.48      ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
% 8.00/1.48      inference(light_normalisation,[status(thm)],[c_29855,c_2013]) ).
% 8.00/1.48  
% 8.00/1.48  cnf(c_29857,plain,
% 8.00/1.48      ( $false ),
% 8.00/1.48      inference(equality_resolution_simp,[status(thm)],[c_29856]) ).
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 8.00/1.48  
% 8.00/1.48  ------                               Statistics
% 8.00/1.48  
% 8.00/1.48  ------ General
% 8.00/1.48  
% 8.00/1.48  abstr_ref_over_cycles:                  0
% 8.00/1.48  abstr_ref_under_cycles:                 0
% 8.00/1.48  gc_basic_clause_elim:                   0
% 8.00/1.48  forced_gc_time:                         0
% 8.00/1.48  parsing_time:                           0.011
% 8.00/1.48  unif_index_cands_time:                  0.
% 8.00/1.48  unif_index_add_time:                    0.
% 8.00/1.48  orderings_time:                         0.
% 8.00/1.48  out_proof_time:                         0.013
% 8.00/1.48  total_time:                             0.976
% 8.00/1.48  num_of_symbols:                         57
% 8.00/1.48  num_of_terms:                           32686
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing
% 8.00/1.48  
% 8.00/1.48  num_of_splits:                          0
% 8.00/1.48  num_of_split_atoms:                     0
% 8.00/1.48  num_of_reused_defs:                     0
% 8.00/1.48  num_eq_ax_congr_red:                    13
% 8.00/1.48  num_of_sem_filtered_clauses:            1
% 8.00/1.48  num_of_subtypes:                        0
% 8.00/1.48  monotx_restored_types:                  0
% 8.00/1.48  sat_num_of_epr_types:                   0
% 8.00/1.48  sat_num_of_non_cyclic_types:            0
% 8.00/1.48  sat_guarded_non_collapsed_types:        0
% 8.00/1.48  num_pure_diseq_elim:                    0
% 8.00/1.48  simp_replaced_by:                       0
% 8.00/1.48  res_preprocessed:                       116
% 8.00/1.48  prep_upred:                             0
% 8.00/1.48  prep_unflattend:                        24
% 8.00/1.48  smt_new_axioms:                         0
% 8.00/1.48  pred_elim_cands:                        3
% 8.00/1.48  pred_elim:                              7
% 8.00/1.48  pred_elim_cl:                           11
% 8.00/1.48  pred_elim_cycles:                       9
% 8.00/1.48  merged_defs:                            0
% 8.00/1.48  merged_defs_ncl:                        0
% 8.00/1.48  bin_hyper_res:                          0
% 8.00/1.48  prep_cycles:                            4
% 8.00/1.48  pred_elim_time:                         0.012
% 8.00/1.48  splitting_time:                         0.
% 8.00/1.48  sem_filter_time:                        0.
% 8.00/1.48  monotx_time:                            0.
% 8.00/1.48  subtype_inf_time:                       0.
% 8.00/1.48  
% 8.00/1.48  ------ Problem properties
% 8.00/1.49  
% 8.00/1.49  clauses:                                18
% 8.00/1.49  conjectures:                            4
% 8.00/1.49  epr:                                    1
% 8.00/1.49  horn:                                   18
% 8.00/1.49  ground:                                 6
% 8.00/1.49  unary:                                  6
% 8.00/1.49  binary:                                 9
% 8.00/1.49  lits:                                   34
% 8.00/1.49  lits_eq:                                9
% 8.00/1.49  fd_pure:                                0
% 8.00/1.49  fd_pseudo:                              0
% 8.00/1.49  fd_cond:                                0
% 8.00/1.49  fd_pseudo_cond:                         0
% 8.00/1.49  ac_symbols:                             0
% 8.00/1.49  
% 8.00/1.49  ------ Propositional Solver
% 8.00/1.49  
% 8.00/1.49  prop_solver_calls:                      39
% 8.00/1.49  prop_fast_solver_calls:                 1354
% 8.00/1.49  smt_solver_calls:                       0
% 8.00/1.49  smt_fast_solver_calls:                  0
% 8.00/1.49  prop_num_of_clauses:                    12038
% 8.00/1.49  prop_preprocess_simplified:             24723
% 8.00/1.49  prop_fo_subsumed:                       36
% 8.00/1.49  prop_solver_time:                       0.
% 8.00/1.49  smt_solver_time:                        0.
% 8.00/1.49  smt_fast_solver_time:                   0.
% 8.00/1.49  prop_fast_solver_time:                  0.
% 8.00/1.49  prop_unsat_core_time:                   0.
% 8.00/1.49  
% 8.00/1.49  ------ QBF
% 8.00/1.49  
% 8.00/1.49  qbf_q_res:                              0
% 8.00/1.49  qbf_num_tautologies:                    0
% 8.00/1.49  qbf_prep_cycles:                        0
% 8.00/1.49  
% 8.00/1.49  ------ BMC1
% 8.00/1.49  
% 8.00/1.49  bmc1_current_bound:                     -1
% 8.00/1.49  bmc1_last_solved_bound:                 -1
% 8.00/1.49  bmc1_unsat_core_size:                   -1
% 8.00/1.49  bmc1_unsat_core_parents_size:           -1
% 8.00/1.49  bmc1_merge_next_fun:                    0
% 8.00/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.00/1.49  
% 8.00/1.49  ------ Instantiation
% 8.00/1.49  
% 8.00/1.49  inst_num_of_clauses:                    3687
% 8.00/1.49  inst_num_in_passive:                    953
% 8.00/1.49  inst_num_in_active:                     1821
% 8.00/1.49  inst_num_in_unprocessed:                913
% 8.00/1.49  inst_num_of_loops:                      1870
% 8.00/1.49  inst_num_of_learning_restarts:          0
% 8.00/1.49  inst_num_moves_active_passive:          39
% 8.00/1.49  inst_lit_activity:                      0
% 8.00/1.49  inst_lit_activity_moves:                1
% 8.00/1.49  inst_num_tautologies:                   0
% 8.00/1.49  inst_num_prop_implied:                  0
% 8.00/1.49  inst_num_existing_simplified:           0
% 8.00/1.49  inst_num_eq_res_simplified:             0
% 8.00/1.49  inst_num_child_elim:                    0
% 8.00/1.49  inst_num_of_dismatching_blockings:      3395
% 8.00/1.49  inst_num_of_non_proper_insts:           5384
% 8.00/1.49  inst_num_of_duplicates:                 0
% 8.00/1.49  inst_inst_num_from_inst_to_res:         0
% 8.00/1.49  inst_dismatching_checking_time:         0.
% 8.00/1.49  
% 8.00/1.49  ------ Resolution
% 8.00/1.49  
% 8.00/1.49  res_num_of_clauses:                     0
% 8.00/1.49  res_num_in_passive:                     0
% 8.00/1.49  res_num_in_active:                      0
% 8.00/1.49  res_num_of_loops:                       120
% 8.00/1.49  res_forward_subset_subsumed:            523
% 8.00/1.49  res_backward_subset_subsumed:           6
% 8.00/1.49  res_forward_subsumed:                   0
% 8.00/1.49  res_backward_subsumed:                  0
% 8.00/1.49  res_forward_subsumption_resolution:     0
% 8.00/1.49  res_backward_subsumption_resolution:    0
% 8.00/1.49  res_clause_to_clause_subsumption:       3905
% 8.00/1.49  res_orphan_elimination:                 0
% 8.00/1.49  res_tautology_del:                      585
% 8.00/1.49  res_num_eq_res_simplified:              1
% 8.00/1.49  res_num_sel_changes:                    0
% 8.00/1.49  res_moves_from_active_to_pass:          0
% 8.00/1.49  
% 8.00/1.49  ------ Superposition
% 8.00/1.49  
% 8.00/1.49  sup_time_total:                         0.
% 8.00/1.49  sup_time_generating:                    0.
% 8.00/1.49  sup_time_sim_full:                      0.
% 8.00/1.49  sup_time_sim_immed:                     0.
% 8.00/1.49  
% 8.00/1.49  sup_num_of_clauses:                     550
% 8.00/1.49  sup_num_in_active:                      357
% 8.00/1.49  sup_num_in_passive:                     193
% 8.00/1.49  sup_num_of_loops:                       372
% 8.00/1.49  sup_fw_superposition:                   519
% 8.00/1.49  sup_bw_superposition:                   336
% 8.00/1.49  sup_immediate_simplified:               55
% 8.00/1.49  sup_given_eliminated:                   0
% 8.00/1.49  comparisons_done:                       0
% 8.00/1.49  comparisons_avoided:                    0
% 8.00/1.49  
% 8.00/1.49  ------ Simplifications
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  sim_fw_subset_subsumed:                 28
% 8.00/1.49  sim_bw_subset_subsumed:                 37
% 8.00/1.49  sim_fw_subsumed:                        3
% 8.00/1.49  sim_bw_subsumed:                        0
% 8.00/1.49  sim_fw_subsumption_res:                 0
% 8.00/1.49  sim_bw_subsumption_res:                 0
% 8.00/1.49  sim_tautology_del:                      2
% 8.00/1.49  sim_eq_tautology_del:                   0
% 8.00/1.49  sim_eq_res_simp:                        0
% 8.00/1.49  sim_fw_demodulated:                     22
% 8.00/1.49  sim_bw_demodulated:                     7
% 8.00/1.49  sim_light_normalised:                   2
% 8.00/1.49  sim_joinable_taut:                      0
% 8.00/1.49  sim_joinable_simp:                      0
% 8.00/1.49  sim_ac_normalised:                      0
% 8.00/1.49  sim_smt_subsumption:                    0
% 8.00/1.49  
%------------------------------------------------------------------------------
