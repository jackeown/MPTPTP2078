%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:35 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 495 expanded)
%              Number of clauses        :  103 ( 159 expanded)
%              Number of leaves         :   18 ( 162 expanded)
%              Depth                    :   25
%              Number of atoms          :  587 (4189 expanded)
%              Number of equality atoms :  146 ( 514 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4)
        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39,f38,f37,f36])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f54,plain,(
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

fof(f62,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_996,plain,
    ( ~ v1_relat_1(X0_53)
    | v1_relat_1(k7_relat_1(X0_53,X0_54)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1300,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k7_relat_1(X0_53,X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_995,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X0_54)),X0_54)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1301,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X0_54)),X0_54) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_995])).

cnf(c_5,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_994,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_53,X0_54)),k2_relat_1(X0_53))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1302,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_53,X0_54)),k2_relat_1(X0_53)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_987,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1308,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_987])).

cnf(c_2,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_292,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_6])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | r1_tarski(k2_relat_1(X0_53),X1_54) ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_1309,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_986])).

cnf(c_2773,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1309])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_997,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ r1_tarski(X2_54,X0_54)
    | r1_tarski(X2_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1299,plain,
    ( r1_tarski(X0_54,X1_54) != iProver_top
    | r1_tarski(X2_54,X0_54) != iProver_top
    | r1_tarski(X2_54,X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_2780,plain,
    ( r1_tarski(X0_54,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0_54,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2773,c_1299])).

cnf(c_2884,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),u1_struct_0(sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_2780])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_993,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1416,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_1417,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1416])).

cnf(c_1419,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_1420,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1419])).

cnf(c_1463,plain,
    ( r1_tarski(X0_54,u1_struct_0(sK1))
    | ~ r1_tarski(X0_54,k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_1590,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),u1_struct_0(sK1))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),k2_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_1592,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),k2_relat_1(sK3)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1590])).

cnf(c_1591,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_1596,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1591])).

cnf(c_2901,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2884,c_37,c_1417,c_1420,c_1592,c_1596])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_991,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ r1_tarski(k1_relat_1(X0_53),X0_54)
    | ~ r1_tarski(k2_relat_1(X0_53),X1_54)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1305,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) = iProver_top
    | r1_tarski(k1_relat_1(X0_53),X0_54) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X1_54) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_992,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k8_relset_1(X0_54,X1_54,X0_53,X1_53) = k10_relat_1(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1304,plain,
    ( k8_relset_1(X0_54,X1_54,X0_53,X1_53) = k10_relat_1(X0_53,X1_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_2057,plain,
    ( k8_relset_1(X0_54,X1_54,X0_53,X1_53) = k10_relat_1(X0_53,X1_53)
    | r1_tarski(k1_relat_1(X0_53),X0_54) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X1_54) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1304])).

cnf(c_4480,plain,
    ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X1_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X1_54),X0_53)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1_54)),X0_54) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X1_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2901,c_2057])).

cnf(c_5715,plain,
    ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53)
    | v1_relat_1(k7_relat_1(sK3,X0_54)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_4480])).

cnf(c_6565,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0_54)) != iProver_top
    | k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5715,c_37,c_1417])).

cnf(c_6566,plain,
    ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53)
    | v1_relat_1(k7_relat_1(sK3,X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6565])).

cnf(c_6573,plain,
    ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_6566])).

cnf(c_7568,plain,
    ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6573,c_37,c_1417])).

cnf(c_1996,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_1308,c_1304])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_402,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_984,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_partfun1(X0_54,X1_54,sK3,X2_54) = k7_relat_1(sK3,X2_54) ),
    inference(subtyping,[status(esa)],[c_402])).

cnf(c_1311,plain,
    ( k2_partfun1(X0_54,X1_54,sK3,X2_54) = k7_relat_1(sK3,X2_54)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_1459,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_54) = k7_relat_1(sK3,X0_54) ),
    inference(superposition,[status(thm)],[c_1308,c_1311])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_308,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_309,plain,
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
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_313,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_26,c_25,c_24])).

cnf(c_314,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_314])).

cnf(c_350,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_354,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_18])).

cnf(c_355,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_420,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_355,c_21])).

cnf(c_421,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_423,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_23,c_22,c_16])).

cnf(c_688,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_423])).

cnf(c_982,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_688])).

cnf(c_1482,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_1459,c_982])).

cnf(c_13,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_990,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1863,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1482,c_990])).

cnf(c_2085,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1996,c_1863])).

cnf(c_7572,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_7568,c_2085])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_989,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1306,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_2087,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1996,c_1306])).

cnf(c_11,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_386,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_387,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_985,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0_53),X0_54)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_1310,plain,
    ( k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53)
    | r1_tarski(k10_relat_1(sK3,X0_53),X0_54) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_1057,plain,
    ( k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53)
    | r1_tarski(k10_relat_1(sK3,X0_53),X0_54) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_1484,plain,
    ( r1_tarski(k10_relat_1(sK3,X0_53),X0_54) != iProver_top
    | k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1310,c_37,c_1057,c_1417])).

cnf(c_1485,plain,
    ( k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53)
    | r1_tarski(k10_relat_1(sK3,X0_53),X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_1484])).

cnf(c_2189,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2087,c_1485])).

cnf(c_7573,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_7572,c_2189])).

cnf(c_7574,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_7573])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.01/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/0.98  
% 3.01/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.98  
% 3.01/0.98  ------  iProver source info
% 3.01/0.98  
% 3.01/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.98  git: non_committed_changes: false
% 3.01/0.98  git: last_make_outside_of_git: false
% 3.01/0.98  
% 3.01/0.98  ------ 
% 3.01/0.98  
% 3.01/0.98  ------ Input Options
% 3.01/0.98  
% 3.01/0.98  --out_options                           all
% 3.01/0.98  --tptp_safe_out                         true
% 3.01/0.98  --problem_path                          ""
% 3.01/0.98  --include_path                          ""
% 3.01/0.98  --clausifier                            res/vclausify_rel
% 3.01/0.98  --clausifier_options                    --mode clausify
% 3.01/0.98  --stdin                                 false
% 3.01/0.98  --stats_out                             all
% 3.01/0.98  
% 3.01/0.98  ------ General Options
% 3.01/0.98  
% 3.01/0.98  --fof                                   false
% 3.01/0.98  --time_out_real                         305.
% 3.01/0.98  --time_out_virtual                      -1.
% 3.01/0.98  --symbol_type_check                     false
% 3.01/0.98  --clausify_out                          false
% 3.01/0.98  --sig_cnt_out                           false
% 3.01/0.98  --trig_cnt_out                          false
% 3.01/0.98  --trig_cnt_out_tolerance                1.
% 3.01/0.98  --trig_cnt_out_sk_spl                   false
% 3.01/0.98  --abstr_cl_out                          false
% 3.01/0.98  
% 3.01/0.98  ------ Global Options
% 3.01/0.98  
% 3.01/0.98  --schedule                              default
% 3.01/0.98  --add_important_lit                     false
% 3.01/0.98  --prop_solver_per_cl                    1000
% 3.01/0.98  --min_unsat_core                        false
% 3.01/0.98  --soft_assumptions                      false
% 3.01/0.98  --soft_lemma_size                       3
% 3.01/0.98  --prop_impl_unit_size                   0
% 3.01/0.98  --prop_impl_unit                        []
% 3.01/0.98  --share_sel_clauses                     true
% 3.01/0.98  --reset_solvers                         false
% 3.01/0.98  --bc_imp_inh                            [conj_cone]
% 3.01/0.98  --conj_cone_tolerance                   3.
% 3.01/0.98  --extra_neg_conj                        none
% 3.01/0.98  --large_theory_mode                     true
% 3.01/0.98  --prolific_symb_bound                   200
% 3.01/0.98  --lt_threshold                          2000
% 3.01/0.98  --clause_weak_htbl                      true
% 3.01/0.98  --gc_record_bc_elim                     false
% 3.01/0.98  
% 3.01/0.98  ------ Preprocessing Options
% 3.01/0.98  
% 3.01/0.98  --preprocessing_flag                    true
% 3.01/0.98  --time_out_prep_mult                    0.1
% 3.01/0.98  --splitting_mode                        input
% 3.01/0.98  --splitting_grd                         true
% 3.01/0.98  --splitting_cvd                         false
% 3.01/0.98  --splitting_cvd_svl                     false
% 3.01/0.98  --splitting_nvd                         32
% 3.01/0.98  --sub_typing                            true
% 3.01/0.98  --prep_gs_sim                           true
% 3.01/0.98  --prep_unflatten                        true
% 3.01/0.98  --prep_res_sim                          true
% 3.01/0.98  --prep_upred                            true
% 3.01/0.98  --prep_sem_filter                       exhaustive
% 3.01/0.98  --prep_sem_filter_out                   false
% 3.01/0.98  --pred_elim                             true
% 3.01/0.98  --res_sim_input                         true
% 3.01/0.98  --eq_ax_congr_red                       true
% 3.01/0.98  --pure_diseq_elim                       true
% 3.01/0.98  --brand_transform                       false
% 3.01/0.98  --non_eq_to_eq                          false
% 3.01/0.98  --prep_def_merge                        true
% 3.01/0.98  --prep_def_merge_prop_impl              false
% 3.01/0.98  --prep_def_merge_mbd                    true
% 3.01/0.98  --prep_def_merge_tr_red                 false
% 3.01/0.98  --prep_def_merge_tr_cl                  false
% 3.01/0.98  --smt_preprocessing                     true
% 3.01/0.98  --smt_ac_axioms                         fast
% 3.01/0.98  --preprocessed_out                      false
% 3.01/0.98  --preprocessed_stats                    false
% 3.01/0.98  
% 3.01/0.98  ------ Abstraction refinement Options
% 3.01/0.98  
% 3.01/0.98  --abstr_ref                             []
% 3.01/0.98  --abstr_ref_prep                        false
% 3.01/0.98  --abstr_ref_until_sat                   false
% 3.01/0.98  --abstr_ref_sig_restrict                funpre
% 3.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.98  --abstr_ref_under                       []
% 3.01/0.98  
% 3.01/0.98  ------ SAT Options
% 3.01/0.98  
% 3.01/0.98  --sat_mode                              false
% 3.01/0.98  --sat_fm_restart_options                ""
% 3.01/0.98  --sat_gr_def                            false
% 3.01/0.98  --sat_epr_types                         true
% 3.01/0.98  --sat_non_cyclic_types                  false
% 3.01/0.98  --sat_finite_models                     false
% 3.01/0.98  --sat_fm_lemmas                         false
% 3.01/0.98  --sat_fm_prep                           false
% 3.01/0.98  --sat_fm_uc_incr                        true
% 3.01/0.98  --sat_out_model                         small
% 3.01/0.98  --sat_out_clauses                       false
% 3.01/0.98  
% 3.01/0.98  ------ QBF Options
% 3.01/0.98  
% 3.01/0.98  --qbf_mode                              false
% 3.01/0.98  --qbf_elim_univ                         false
% 3.01/0.98  --qbf_dom_inst                          none
% 3.01/0.98  --qbf_dom_pre_inst                      false
% 3.01/0.98  --qbf_sk_in                             false
% 3.01/0.98  --qbf_pred_elim                         true
% 3.01/0.98  --qbf_split                             512
% 3.01/0.98  
% 3.01/0.98  ------ BMC1 Options
% 3.01/0.98  
% 3.01/0.98  --bmc1_incremental                      false
% 3.01/0.98  --bmc1_axioms                           reachable_all
% 3.01/0.98  --bmc1_min_bound                        0
% 3.01/0.98  --bmc1_max_bound                        -1
% 3.01/0.98  --bmc1_max_bound_default                -1
% 3.01/0.98  --bmc1_symbol_reachability              true
% 3.01/0.98  --bmc1_property_lemmas                  false
% 3.01/0.98  --bmc1_k_induction                      false
% 3.01/0.98  --bmc1_non_equiv_states                 false
% 3.01/0.98  --bmc1_deadlock                         false
% 3.01/0.98  --bmc1_ucm                              false
% 3.01/0.98  --bmc1_add_unsat_core                   none
% 3.01/0.98  --bmc1_unsat_core_children              false
% 3.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.98  --bmc1_out_stat                         full
% 3.01/0.98  --bmc1_ground_init                      false
% 3.01/0.98  --bmc1_pre_inst_next_state              false
% 3.01/0.98  --bmc1_pre_inst_state                   false
% 3.01/0.98  --bmc1_pre_inst_reach_state             false
% 3.01/0.98  --bmc1_out_unsat_core                   false
% 3.01/0.98  --bmc1_aig_witness_out                  false
% 3.01/0.98  --bmc1_verbose                          false
% 3.01/0.98  --bmc1_dump_clauses_tptp                false
% 3.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.98  --bmc1_dump_file                        -
% 3.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.98  --bmc1_ucm_extend_mode                  1
% 3.01/0.98  --bmc1_ucm_init_mode                    2
% 3.01/0.98  --bmc1_ucm_cone_mode                    none
% 3.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.98  --bmc1_ucm_relax_model                  4
% 3.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.98  --bmc1_ucm_layered_model                none
% 3.01/0.98  --bmc1_ucm_max_lemma_size               10
% 3.01/0.98  
% 3.01/0.98  ------ AIG Options
% 3.01/0.98  
% 3.01/0.98  --aig_mode                              false
% 3.01/0.98  
% 3.01/0.98  ------ Instantiation Options
% 3.01/0.98  
% 3.01/0.98  --instantiation_flag                    true
% 3.01/0.98  --inst_sos_flag                         false
% 3.01/0.98  --inst_sos_phase                        true
% 3.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.98  --inst_lit_sel_side                     num_symb
% 3.01/0.98  --inst_solver_per_active                1400
% 3.01/0.98  --inst_solver_calls_frac                1.
% 3.01/0.98  --inst_passive_queue_type               priority_queues
% 3.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.98  --inst_passive_queues_freq              [25;2]
% 3.01/0.98  --inst_dismatching                      true
% 3.01/0.98  --inst_eager_unprocessed_to_passive     true
% 3.01/0.98  --inst_prop_sim_given                   true
% 3.01/0.98  --inst_prop_sim_new                     false
% 3.01/0.98  --inst_subs_new                         false
% 3.01/0.98  --inst_eq_res_simp                      false
% 3.01/0.98  --inst_subs_given                       false
% 3.01/0.98  --inst_orphan_elimination               true
% 3.01/0.98  --inst_learning_loop_flag               true
% 3.01/0.98  --inst_learning_start                   3000
% 3.01/0.98  --inst_learning_factor                  2
% 3.01/0.98  --inst_start_prop_sim_after_learn       3
% 3.01/0.98  --inst_sel_renew                        solver
% 3.01/0.98  --inst_lit_activity_flag                true
% 3.01/0.98  --inst_restr_to_given                   false
% 3.01/0.98  --inst_activity_threshold               500
% 3.01/0.98  --inst_out_proof                        true
% 3.01/0.98  
% 3.01/0.98  ------ Resolution Options
% 3.01/0.98  
% 3.01/0.98  --resolution_flag                       true
% 3.01/0.98  --res_lit_sel                           adaptive
% 3.01/0.98  --res_lit_sel_side                      none
% 3.01/0.98  --res_ordering                          kbo
% 3.01/0.98  --res_to_prop_solver                    active
% 3.01/0.98  --res_prop_simpl_new                    false
% 3.01/0.98  --res_prop_simpl_given                  true
% 3.01/0.98  --res_passive_queue_type                priority_queues
% 3.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.98  --res_passive_queues_freq               [15;5]
% 3.01/0.98  --res_forward_subs                      full
% 3.01/0.98  --res_backward_subs                     full
% 3.01/0.98  --res_forward_subs_resolution           true
% 3.01/0.98  --res_backward_subs_resolution          true
% 3.01/0.98  --res_orphan_elimination                true
% 3.01/0.98  --res_time_limit                        2.
% 3.01/0.98  --res_out_proof                         true
% 3.01/0.98  
% 3.01/0.98  ------ Superposition Options
% 3.01/0.98  
% 3.01/0.98  --superposition_flag                    true
% 3.01/0.98  --sup_passive_queue_type                priority_queues
% 3.01/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.98  --demod_completeness_check              fast
% 3.01/0.98  --demod_use_ground                      true
% 3.01/0.98  --sup_to_prop_solver                    passive
% 3.01/0.98  --sup_prop_simpl_new                    true
% 3.01/0.98  --sup_prop_simpl_given                  true
% 3.01/0.98  --sup_fun_splitting                     false
% 3.01/0.98  --sup_smt_interval                      50000
% 3.01/0.98  
% 3.01/0.98  ------ Superposition Simplification Setup
% 3.01/0.98  
% 3.01/0.98  --sup_indices_passive                   []
% 3.01/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.98  --sup_full_bw                           [BwDemod]
% 3.01/0.98  --sup_immed_triv                        [TrivRules]
% 3.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.98  --sup_immed_bw_main                     []
% 3.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.98  
% 3.01/0.98  ------ Combination Options
% 3.01/0.98  
% 3.01/0.98  --comb_res_mult                         3
% 3.01/0.98  --comb_sup_mult                         2
% 3.01/0.98  --comb_inst_mult                        10
% 3.01/0.98  
% 3.01/0.98  ------ Debug Options
% 3.01/0.98  
% 3.01/0.98  --dbg_backtrace                         false
% 3.01/0.98  --dbg_dump_prop_clauses                 false
% 3.01/0.98  --dbg_dump_prop_clauses_file            -
% 3.01/0.98  --dbg_out_stat                          false
% 3.01/0.98  ------ Parsing...
% 3.01/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.98  
% 3.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.01/0.98  
% 3.01/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.98  
% 3.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.98  ------ Proving...
% 3.01/0.98  ------ Problem Properties 
% 3.01/0.98  
% 3.01/0.98  
% 3.01/0.98  clauses                                 16
% 3.01/0.98  conjectures                             4
% 3.01/0.98  EPR                                     1
% 3.01/0.98  Horn                                    16
% 3.01/0.98  unary                                   5
% 3.01/0.98  binary                                  7
% 3.01/0.98  lits                                    32
% 3.01/0.98  lits eq                                 7
% 3.01/0.98  fd_pure                                 0
% 3.01/0.98  fd_pseudo                               0
% 3.01/0.98  fd_cond                                 0
% 3.01/0.98  fd_pseudo_cond                          0
% 3.01/0.98  AC symbols                              0
% 3.01/0.98  
% 3.01/0.98  ------ Schedule dynamic 5 is on 
% 3.01/0.98  
% 3.01/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/0.98  
% 3.01/0.98  
% 3.01/0.98  ------ 
% 3.01/0.98  Current options:
% 3.01/0.98  ------ 
% 3.01/0.98  
% 3.01/0.98  ------ Input Options
% 3.01/0.98  
% 3.01/0.98  --out_options                           all
% 3.01/0.98  --tptp_safe_out                         true
% 3.01/0.98  --problem_path                          ""
% 3.01/0.98  --include_path                          ""
% 3.01/0.98  --clausifier                            res/vclausify_rel
% 3.01/0.98  --clausifier_options                    --mode clausify
% 3.01/0.98  --stdin                                 false
% 3.01/0.98  --stats_out                             all
% 3.01/0.98  
% 3.01/0.98  ------ General Options
% 3.01/0.98  
% 3.01/0.98  --fof                                   false
% 3.01/0.98  --time_out_real                         305.
% 3.01/0.98  --time_out_virtual                      -1.
% 3.01/0.98  --symbol_type_check                     false
% 3.01/0.98  --clausify_out                          false
% 3.01/0.98  --sig_cnt_out                           false
% 3.01/0.98  --trig_cnt_out                          false
% 3.01/0.98  --trig_cnt_out_tolerance                1.
% 3.01/0.98  --trig_cnt_out_sk_spl                   false
% 3.01/0.98  --abstr_cl_out                          false
% 3.01/0.98  
% 3.01/0.98  ------ Global Options
% 3.01/0.98  
% 3.01/0.98  --schedule                              default
% 3.01/0.98  --add_important_lit                     false
% 3.01/0.98  --prop_solver_per_cl                    1000
% 3.01/0.98  --min_unsat_core                        false
% 3.01/0.98  --soft_assumptions                      false
% 3.01/0.98  --soft_lemma_size                       3
% 3.01/0.98  --prop_impl_unit_size                   0
% 3.01/0.98  --prop_impl_unit                        []
% 3.01/0.98  --share_sel_clauses                     true
% 3.01/0.98  --reset_solvers                         false
% 3.01/0.98  --bc_imp_inh                            [conj_cone]
% 3.01/0.98  --conj_cone_tolerance                   3.
% 3.01/0.98  --extra_neg_conj                        none
% 3.01/0.98  --large_theory_mode                     true
% 3.01/0.98  --prolific_symb_bound                   200
% 3.01/0.98  --lt_threshold                          2000
% 3.01/0.98  --clause_weak_htbl                      true
% 3.01/0.98  --gc_record_bc_elim                     false
% 3.01/0.98  
% 3.01/0.98  ------ Preprocessing Options
% 3.01/0.98  
% 3.01/0.98  --preprocessing_flag                    true
% 3.01/0.98  --time_out_prep_mult                    0.1
% 3.01/0.98  --splitting_mode                        input
% 3.01/0.98  --splitting_grd                         true
% 3.01/0.98  --splitting_cvd                         false
% 3.01/0.98  --splitting_cvd_svl                     false
% 3.01/0.98  --splitting_nvd                         32
% 3.01/0.98  --sub_typing                            true
% 3.01/0.98  --prep_gs_sim                           true
% 3.01/0.98  --prep_unflatten                        true
% 3.01/0.98  --prep_res_sim                          true
% 3.01/0.98  --prep_upred                            true
% 3.01/0.98  --prep_sem_filter                       exhaustive
% 3.01/0.98  --prep_sem_filter_out                   false
% 3.01/0.98  --pred_elim                             true
% 3.01/0.98  --res_sim_input                         true
% 3.01/0.98  --eq_ax_congr_red                       true
% 3.01/0.98  --pure_diseq_elim                       true
% 3.01/0.98  --brand_transform                       false
% 3.01/0.98  --non_eq_to_eq                          false
% 3.01/0.98  --prep_def_merge                        true
% 3.01/0.98  --prep_def_merge_prop_impl              false
% 3.01/0.98  --prep_def_merge_mbd                    true
% 3.01/0.98  --prep_def_merge_tr_red                 false
% 3.01/0.98  --prep_def_merge_tr_cl                  false
% 3.01/0.98  --smt_preprocessing                     true
% 3.01/0.98  --smt_ac_axioms                         fast
% 3.01/0.98  --preprocessed_out                      false
% 3.01/0.98  --preprocessed_stats                    false
% 3.01/0.98  
% 3.01/0.98  ------ Abstraction refinement Options
% 3.01/0.98  
% 3.01/0.98  --abstr_ref                             []
% 3.01/0.98  --abstr_ref_prep                        false
% 3.01/0.98  --abstr_ref_until_sat                   false
% 3.01/0.98  --abstr_ref_sig_restrict                funpre
% 3.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.98  --abstr_ref_under                       []
% 3.01/0.98  
% 3.01/0.98  ------ SAT Options
% 3.01/0.98  
% 3.01/0.98  --sat_mode                              false
% 3.01/0.98  --sat_fm_restart_options                ""
% 3.01/0.98  --sat_gr_def                            false
% 3.01/0.98  --sat_epr_types                         true
% 3.01/0.98  --sat_non_cyclic_types                  false
% 3.01/0.98  --sat_finite_models                     false
% 3.01/0.98  --sat_fm_lemmas                         false
% 3.01/0.98  --sat_fm_prep                           false
% 3.01/0.98  --sat_fm_uc_incr                        true
% 3.01/0.98  --sat_out_model                         small
% 3.01/0.98  --sat_out_clauses                       false
% 3.01/0.98  
% 3.01/0.98  ------ QBF Options
% 3.01/0.98  
% 3.01/0.98  --qbf_mode                              false
% 3.01/0.98  --qbf_elim_univ                         false
% 3.01/0.98  --qbf_dom_inst                          none
% 3.01/0.98  --qbf_dom_pre_inst                      false
% 3.01/0.98  --qbf_sk_in                             false
% 3.01/0.98  --qbf_pred_elim                         true
% 3.01/0.98  --qbf_split                             512
% 3.01/0.98  
% 3.01/0.98  ------ BMC1 Options
% 3.01/0.98  
% 3.01/0.98  --bmc1_incremental                      false
% 3.01/0.98  --bmc1_axioms                           reachable_all
% 3.01/0.98  --bmc1_min_bound                        0
% 3.01/0.98  --bmc1_max_bound                        -1
% 3.01/0.98  --bmc1_max_bound_default                -1
% 3.01/0.98  --bmc1_symbol_reachability              true
% 3.01/0.98  --bmc1_property_lemmas                  false
% 3.01/0.98  --bmc1_k_induction                      false
% 3.01/0.98  --bmc1_non_equiv_states                 false
% 3.01/0.98  --bmc1_deadlock                         false
% 3.01/0.98  --bmc1_ucm                              false
% 3.01/0.98  --bmc1_add_unsat_core                   none
% 3.01/0.98  --bmc1_unsat_core_children              false
% 3.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.98  --bmc1_out_stat                         full
% 3.01/0.98  --bmc1_ground_init                      false
% 3.01/0.98  --bmc1_pre_inst_next_state              false
% 3.01/0.98  --bmc1_pre_inst_state                   false
% 3.01/0.98  --bmc1_pre_inst_reach_state             false
% 3.01/0.98  --bmc1_out_unsat_core                   false
% 3.01/0.98  --bmc1_aig_witness_out                  false
% 3.01/0.98  --bmc1_verbose                          false
% 3.01/0.98  --bmc1_dump_clauses_tptp                false
% 3.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.98  --bmc1_dump_file                        -
% 3.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.98  --bmc1_ucm_extend_mode                  1
% 3.01/0.98  --bmc1_ucm_init_mode                    2
% 3.01/0.98  --bmc1_ucm_cone_mode                    none
% 3.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.98  --bmc1_ucm_relax_model                  4
% 3.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.98  --bmc1_ucm_layered_model                none
% 3.01/0.98  --bmc1_ucm_max_lemma_size               10
% 3.01/0.98  
% 3.01/0.98  ------ AIG Options
% 3.01/0.98  
% 3.01/0.98  --aig_mode                              false
% 3.01/0.98  
% 3.01/0.98  ------ Instantiation Options
% 3.01/0.98  
% 3.01/0.98  --instantiation_flag                    true
% 3.01/0.98  --inst_sos_flag                         false
% 3.01/0.98  --inst_sos_phase                        true
% 3.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.98  --inst_lit_sel_side                     none
% 3.01/0.98  --inst_solver_per_active                1400
% 3.01/0.98  --inst_solver_calls_frac                1.
% 3.01/0.98  --inst_passive_queue_type               priority_queues
% 3.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.98  --inst_passive_queues_freq              [25;2]
% 3.01/0.98  --inst_dismatching                      true
% 3.01/0.98  --inst_eager_unprocessed_to_passive     true
% 3.01/0.98  --inst_prop_sim_given                   true
% 3.01/0.98  --inst_prop_sim_new                     false
% 3.01/0.98  --inst_subs_new                         false
% 3.01/0.98  --inst_eq_res_simp                      false
% 3.01/0.98  --inst_subs_given                       false
% 3.01/0.98  --inst_orphan_elimination               true
% 3.01/0.98  --inst_learning_loop_flag               true
% 3.01/0.98  --inst_learning_start                   3000
% 3.01/0.98  --inst_learning_factor                  2
% 3.01/0.98  --inst_start_prop_sim_after_learn       3
% 3.01/0.98  --inst_sel_renew                        solver
% 3.01/0.98  --inst_lit_activity_flag                true
% 3.01/0.98  --inst_restr_to_given                   false
% 3.01/0.98  --inst_activity_threshold               500
% 3.01/0.98  --inst_out_proof                        true
% 3.01/0.98  
% 3.01/0.98  ------ Resolution Options
% 3.01/0.98  
% 3.01/0.98  --resolution_flag                       false
% 3.01/0.98  --res_lit_sel                           adaptive
% 3.01/0.98  --res_lit_sel_side                      none
% 3.01/0.98  --res_ordering                          kbo
% 3.01/0.98  --res_to_prop_solver                    active
% 3.01/0.98  --res_prop_simpl_new                    false
% 3.01/0.98  --res_prop_simpl_given                  true
% 3.01/0.98  --res_passive_queue_type                priority_queues
% 3.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.98  --res_passive_queues_freq               [15;5]
% 3.01/0.98  --res_forward_subs                      full
% 3.01/0.98  --res_backward_subs                     full
% 3.01/0.98  --res_forward_subs_resolution           true
% 3.01/0.98  --res_backward_subs_resolution          true
% 3.01/0.98  --res_orphan_elimination                true
% 3.01/0.98  --res_time_limit                        2.
% 3.01/0.98  --res_out_proof                         true
% 3.01/0.98  
% 3.01/0.98  ------ Superposition Options
% 3.01/0.98  
% 3.01/0.98  --superposition_flag                    true
% 3.01/0.98  --sup_passive_queue_type                priority_queues
% 3.01/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.98  --demod_completeness_check              fast
% 3.01/0.98  --demod_use_ground                      true
% 3.01/0.98  --sup_to_prop_solver                    passive
% 3.01/0.98  --sup_prop_simpl_new                    true
% 3.01/0.98  --sup_prop_simpl_given                  true
% 3.01/0.98  --sup_fun_splitting                     false
% 3.01/0.98  --sup_smt_interval                      50000
% 3.01/0.98  
% 3.01/0.98  ------ Superposition Simplification Setup
% 3.01/0.98  
% 3.01/0.98  --sup_indices_passive                   []
% 3.01/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.98  --sup_full_bw                           [BwDemod]
% 3.01/0.98  --sup_immed_triv                        [TrivRules]
% 3.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.98  --sup_immed_bw_main                     []
% 3.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.98  
% 3.01/0.98  ------ Combination Options
% 3.01/0.98  
% 3.01/0.98  --comb_res_mult                         3
% 3.01/0.98  --comb_sup_mult                         2
% 3.01/0.98  --comb_inst_mult                        10
% 3.01/0.98  
% 3.01/0.98  ------ Debug Options
% 3.01/0.98  
% 3.01/0.98  --dbg_backtrace                         false
% 3.01/0.98  --dbg_dump_prop_clauses                 false
% 3.01/0.98  --dbg_dump_prop_clauses_file            -
% 3.01/0.98  --dbg_out_stat                          false
% 3.01/0.98  
% 3.01/0.98  
% 3.01/0.98  
% 3.01/0.98  
% 3.01/0.98  ------ Proving...
% 3.01/0.98  
% 3.01/0.98  
% 3.01/0.98  % SZS status Theorem for theBenchmark.p
% 3.01/0.98  
% 3.01/0.98   Resolution empty clause
% 3.01/0.98  
% 3.01/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/0.98  
% 3.01/0.98  fof(f3,axiom,(
% 3.01/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f19,plain,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f3])).
% 3.01/0.99  
% 3.01/0.99  fof(f45,plain,(
% 3.01/0.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f19])).
% 3.01/0.99  
% 3.01/0.99  fof(f4,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f20,plain,(
% 3.01/0.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f4])).
% 3.01/0.99  
% 3.01/0.99  fof(f46,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f5,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f21,plain,(
% 3.01/0.99    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f5])).
% 3.01/0.99  
% 3.01/0.99  fof(f47,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f21])).
% 3.01/0.99  
% 3.01/0.99  fof(f13,conjecture,(
% 3.01/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f14,negated_conjecture,(
% 3.01/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 3.01/0.99    inference(negated_conjecture,[],[f13])).
% 3.01/0.99  
% 3.01/0.99  fof(f33,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f14])).
% 3.01/0.99  
% 3.01/0.99  fof(f34,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f33])).
% 3.01/0.99  
% 3.01/0.99  fof(f40,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f39,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f38,plain,(
% 3.01/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f37,plain,(
% 3.01/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f36,plain,(
% 3.01/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f41,plain,(
% 3.01/0.99    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39,f38,f37,f36])).
% 3.01/0.99  
% 3.01/0.99  fof(f65,plain,(
% 3.01/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f2,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f18,plain,(
% 3.01/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f2])).
% 3.01/0.99  
% 3.01/0.99  fof(f35,plain,(
% 3.01/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(nnf_transformation,[],[f18])).
% 3.01/0.99  
% 3.01/0.99  fof(f43,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f35])).
% 3.01/0.99  
% 3.01/0.99  fof(f7,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f15,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.01/0.99    inference(pure_predicate_removal,[],[f7])).
% 3.01/0.99  
% 3.01/0.99  fof(f23,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.99    inference(ennf_transformation,[],[f15])).
% 3.01/0.99  
% 3.01/0.99  fof(f49,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f23])).
% 3.01/0.99  
% 3.01/0.99  fof(f6,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f22,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.99    inference(ennf_transformation,[],[f6])).
% 3.01/0.99  
% 3.01/0.99  fof(f48,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f1,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f16,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.01/0.99    inference(ennf_transformation,[],[f1])).
% 3.01/0.99  
% 3.01/0.99  fof(f17,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.01/0.99    inference(flattening,[],[f16])).
% 3.01/0.99  
% 3.01/0.99  fof(f42,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f17])).
% 3.01/0.99  
% 3.01/0.99  fof(f9,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f25,plain,(
% 3.01/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.01/0.99    inference(ennf_transformation,[],[f9])).
% 3.01/0.99  
% 3.01/0.99  fof(f26,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.01/0.99    inference(flattening,[],[f25])).
% 3.01/0.99  
% 3.01/0.99  fof(f51,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f26])).
% 3.01/0.99  
% 3.01/0.99  fof(f8,axiom,(
% 3.01/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f24,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.99    inference(ennf_transformation,[],[f8])).
% 3.01/0.99  
% 3.01/0.99  fof(f50,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f24])).
% 3.01/0.99  
% 3.01/0.99  fof(f10,axiom,(
% 3.01/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f27,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.01/0.99    inference(ennf_transformation,[],[f10])).
% 3.01/0.99  
% 3.01/0.99  fof(f28,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.01/0.99    inference(flattening,[],[f27])).
% 3.01/0.99  
% 3.01/0.99  fof(f52,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f28])).
% 3.01/0.99  
% 3.01/0.99  fof(f63,plain,(
% 3.01/0.99    v1_funct_1(sK3)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f64,plain,(
% 3.01/0.99    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f12,axiom,(
% 3.01/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f31,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f12])).
% 3.01/0.99  
% 3.01/0.99  fof(f32,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/0.99    inference(flattening,[],[f31])).
% 3.01/0.99  
% 3.01/0.99  fof(f54,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f32])).
% 3.01/0.99  
% 3.01/0.99  fof(f62,plain,(
% 3.01/0.99    m1_pre_topc(sK2,sK0)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f55,plain,(
% 3.01/0.99    ~v2_struct_0(sK0)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f56,plain,(
% 3.01/0.99    v2_pre_topc(sK0)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f57,plain,(
% 3.01/0.99    l1_pre_topc(sK0)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f60,plain,(
% 3.01/0.99    l1_pre_topc(sK1)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f58,plain,(
% 3.01/0.99    ~v2_struct_0(sK1)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f59,plain,(
% 3.01/0.99    v2_pre_topc(sK1)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f68,plain,(
% 3.01/0.99    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f67,plain,(
% 3.01/0.99    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 3.01/0.99    inference(cnf_transformation,[],[f41])).
% 3.01/0.99  
% 3.01/0.99  fof(f11,axiom,(
% 3.01/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f29,plain,(
% 3.01/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f11])).
% 3.01/0.99  
% 3.01/0.99  fof(f30,plain,(
% 3.01/0.99    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/0.99    inference(flattening,[],[f29])).
% 3.01/0.99  
% 3.01/0.99  fof(f53,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f30])).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_996,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0_53) | v1_relat_1(k7_relat_1(X0_53,X0_54)) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1300,plain,
% 3.01/0.99      ( v1_relat_1(X0_53) != iProver_top
% 3.01/0.99      | v1_relat_1(k7_relat_1(X0_53,X0_54)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4,plain,
% 3.01/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_995,plain,
% 3.01/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X0_54)),X0_54)
% 3.01/0.99      | ~ v1_relat_1(X0_53) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1301,plain,
% 3.01/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X0_54)),X0_54) = iProver_top
% 3.01/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_995]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 3.01/0.99      | ~ v1_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_994,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(X0_53,X0_54)),k2_relat_1(X0_53))
% 3.01/0.99      | ~ v1_relat_1(X0_53) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1302,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(X0_53,X0_54)),k2_relat_1(X0_53)) = iProver_top
% 3.01/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_16,negated_conjecture,
% 3.01/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.01/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_987,negated_conjecture,
% 3.01/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1308,plain,
% 3.01/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_987]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2,plain,
% 3.01/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_287,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | r1_tarski(k2_relat_1(X3),X4)
% 3.01/0.99      | ~ v1_relat_1(X3)
% 3.01/0.99      | X0 != X3
% 3.01/0.99      | X2 != X4 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_288,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.01/0.99      | ~ v1_relat_1(X0) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_287]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_292,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.01/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.01/0.99      inference(global_propositional_subsumption,[status(thm)],[c_288,c_6]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_293,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_292]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_986,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.01/0.99      | r1_tarski(k2_relat_1(X0_53),X1_54) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_293]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1309,plain,
% 3.01/0.99      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 3.01/0.99      | r1_tarski(k2_relat_1(X0_53),X1_54) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_986]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2773,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1308,c_1309]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_0,plain,
% 3.01/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_997,plain,
% 3.01/0.99      ( ~ r1_tarski(X0_54,X1_54)
% 3.01/0.99      | ~ r1_tarski(X2_54,X0_54)
% 3.01/0.99      | r1_tarski(X2_54,X1_54) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1299,plain,
% 3.01/0.99      ( r1_tarski(X0_54,X1_54) != iProver_top
% 3.01/0.99      | r1_tarski(X2_54,X0_54) != iProver_top
% 3.01/0.99      | r1_tarski(X2_54,X1_54) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2780,plain,
% 3.01/0.99      ( r1_tarski(X0_54,u1_struct_0(sK1)) = iProver_top
% 3.01/0.99      | r1_tarski(X0_54,k2_relat_1(sK3)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2773,c_1299]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2884,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),u1_struct_0(sK1)) = iProver_top
% 3.01/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1302,c_2780]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_37,plain,
% 3.01/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_993,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.01/0.99      | v1_relat_1(X0_53) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1416,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.99      | v1_relat_1(sK3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_993]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1417,plain,
% 3.01/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.01/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1416]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1419,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.99      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_986]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1420,plain,
% 3.01/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.01/0.99      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1419]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1463,plain,
% 3.01/0.99      ( r1_tarski(X0_54,u1_struct_0(sK1))
% 3.01/0.99      | ~ r1_tarski(X0_54,k2_relat_1(sK3))
% 3.01/0.99      | ~ r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_997]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1590,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),u1_struct_0(sK1))
% 3.01/0.99      | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),k2_relat_1(sK3))
% 3.01/0.99      | ~ r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1463]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1592,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),u1_struct_0(sK1)) = iProver_top
% 3.01/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),k2_relat_1(sK3)) != iProver_top
% 3.01/0.99      | r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1590]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1591,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),k2_relat_1(sK3))
% 3.01/0.99      | ~ v1_relat_1(sK3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_994]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1596,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),k2_relat_1(sK3)) = iProver_top
% 3.01/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1591]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2901,plain,
% 3.01/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_54)),u1_struct_0(sK1)) = iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_2884,c_37,c_1417,c_1420,c_1592,c_1596]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9,plain,
% 3.01/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.01/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.01/0.99      | ~ v1_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_991,plain,
% 3.01/0.99      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.01/0.99      | ~ r1_tarski(k1_relat_1(X0_53),X0_54)
% 3.01/0.99      | ~ r1_tarski(k2_relat_1(X0_53),X1_54)
% 3.01/0.99      | ~ v1_relat_1(X0_53) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1305,plain,
% 3.01/0.99      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) = iProver_top
% 3.01/0.99      | r1_tarski(k1_relat_1(X0_53),X0_54) != iProver_top
% 3.01/0.99      | r1_tarski(k2_relat_1(X0_53),X1_54) != iProver_top
% 3.01/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_991]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_8,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_992,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.01/0.99      | k8_relset_1(X0_54,X1_54,X0_53,X1_53) = k10_relat_1(X0_53,X1_53) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1304,plain,
% 3.01/0.99      ( k8_relset_1(X0_54,X1_54,X0_53,X1_53) = k10_relat_1(X0_53,X1_53)
% 3.01/0.99      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2057,plain,
% 3.01/0.99      ( k8_relset_1(X0_54,X1_54,X0_53,X1_53) = k10_relat_1(X0_53,X1_53)
% 3.01/0.99      | r1_tarski(k1_relat_1(X0_53),X0_54) != iProver_top
% 3.01/0.99      | r1_tarski(k2_relat_1(X0_53),X1_54) != iProver_top
% 3.01/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1305,c_1304]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4480,plain,
% 3.01/0.99      ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X1_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X1_54),X0_53)
% 3.01/0.99      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1_54)),X0_54) != iProver_top
% 3.01/0.99      | v1_relat_1(k7_relat_1(sK3,X1_54)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2901,c_2057]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_5715,plain,
% 3.01/0.99      ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53)
% 3.01/0.99      | v1_relat_1(k7_relat_1(sK3,X0_54)) != iProver_top
% 3.01/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1301,c_4480]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6565,plain,
% 3.01/0.99      ( v1_relat_1(k7_relat_1(sK3,X0_54)) != iProver_top
% 3.01/0.99      | k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_5715,c_37,c_1417]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6566,plain,
% 3.01/0.99      ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53)
% 3.01/0.99      | v1_relat_1(k7_relat_1(sK3,X0_54)) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_6565]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6573,plain,
% 3.01/0.99      ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53)
% 3.01/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1300,c_6566]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7568,plain,
% 3.01/0.99      ( k8_relset_1(X0_54,u1_struct_0(sK1),k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_6573,c_37,c_1417]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1996,plain,
% 3.01/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1308,c_1304]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_10,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_18,negated_conjecture,
% 3.01/0.99      ( v1_funct_1(sK3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_401,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_402,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.01/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_984,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.01/0.99      | k2_partfun1(X0_54,X1_54,sK3,X2_54) = k7_relat_1(sK3,X2_54) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_402]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1311,plain,
% 3.01/0.99      ( k2_partfun1(X0_54,X1_54,sK3,X2_54) = k7_relat_1(sK3,X2_54)
% 3.01/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1459,plain,
% 3.01/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_54) = k7_relat_1(sK3,X0_54) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1308,c_1311]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_17,negated_conjecture,
% 3.01/0.99      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_12,plain,
% 3.01/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.01/0.99      | ~ m1_pre_topc(X3,X1)
% 3.01/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | v2_struct_0(X2)
% 3.01/0.99      | ~ v2_pre_topc(X2)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X2)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_19,negated_conjecture,
% 3.01/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_308,plain,
% 3.01/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.01/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.01/0.99      | v2_struct_0(X2)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X2)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X2)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 3.01/0.99      | sK2 != X3
% 3.01/0.99      | sK0 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_309,plain,
% 3.01/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.01/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | v2_struct_0(sK0)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ v2_pre_topc(sK0)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(sK0)
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_26,negated_conjecture,
% 3.01/0.99      ( ~ v2_struct_0(sK0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_25,negated_conjecture,
% 3.01/0.99      ( v2_pre_topc(sK0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_24,negated_conjecture,
% 3.01/0.99      ( l1_pre_topc(sK0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_313,plain,
% 3.01/0.99      ( ~ l1_pre_topc(X1)
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.01/0.99      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_309,c_26,c_25,c_24]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_314,plain,
% 3.01/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.01/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_313]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_349,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.01/0.99      | v2_struct_0(X1)
% 3.01/0.99      | ~ v2_pre_topc(X1)
% 3.01/0.99      | ~ l1_pre_topc(X1)
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
% 3.01/0.99      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/0.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_314]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_350,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.01/0.99      | v2_struct_0(X0)
% 3.01/0.99      | ~ v2_pre_topc(X0)
% 3.01/0.99      | ~ l1_pre_topc(X0)
% 3.01/0.99      | ~ v1_funct_1(sK3)
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 3.01/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_349]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_354,plain,
% 3.01/0.99      ( ~ l1_pre_topc(X0)
% 3.01/0.99      | ~ v2_pre_topc(X0)
% 3.01/0.99      | v2_struct_0(X0)
% 3.01/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 3.01/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 3.01/0.99      inference(global_propositional_subsumption,[status(thm)],[c_350,c_18]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_355,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.01/0.99      | v2_struct_0(X0)
% 3.01/0.99      | ~ v2_pre_topc(X0)
% 3.01/0.99      | ~ l1_pre_topc(X0)
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 3.01/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_354]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_21,negated_conjecture,
% 3.01/0.99      ( l1_pre_topc(sK1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_420,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 3.01/0.99      | v2_struct_0(X0)
% 3.01/0.99      | ~ v2_pre_topc(X0)
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 3.01/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 3.01/0.99      | sK1 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_355,c_21]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_421,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.99      | v2_struct_0(sK1)
% 3.01/0.99      | ~ v2_pre_topc(sK1)
% 3.01/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 3.01/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_23,negated_conjecture,
% 3.01/0.99      ( ~ v2_struct_0(sK1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_22,negated_conjecture,
% 3.01/0.99      ( v2_pre_topc(sK1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_423,plain,
% 3.01/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 3.01/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_421,c_23,c_22,c_16]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_688,plain,
% 3.01/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 3.01/0.99      inference(equality_resolution_simp,[status(thm)],[c_423]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_982,plain,
% 3.01/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_688]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1482,plain,
% 3.01/0.99      ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 3.01/0.99      inference(demodulation,[status(thm)],[c_1459,c_982]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_13,negated_conjecture,
% 3.01/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 3.01/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_990,negated_conjecture,
% 3.01/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1863,plain,
% 3.01/0.99      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
% 3.01/0.99      inference(demodulation,[status(thm)],[c_1482,c_990]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2085,plain,
% 3.01/0.99      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 3.01/0.99      inference(demodulation,[status(thm)],[c_1996,c_1863]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7572,plain,
% 3.01/0.99      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 3.01/0.99      inference(demodulation,[status(thm)],[c_7568,c_2085]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_14,negated_conjecture,
% 3.01/0.99      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_989,negated_conjecture,
% 3.01/0.99      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1306,plain,
% 3.01/0.99      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2087,plain,
% 3.01/0.99      ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 3.01/0.99      inference(demodulation,[status(thm)],[c_1996,c_1306]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_11,plain,
% 3.01/0.99      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | ~ v1_relat_1(X0)
% 3.01/0.99      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_386,plain,
% 3.01/0.99      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 3.01/0.99      | ~ v1_relat_1(X0)
% 3.01/0.99      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_387,plain,
% 3.01/0.99      ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
% 3.01/0.99      | ~ v1_relat_1(sK3)
% 3.01/0.99      | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_985,plain,
% 3.01/0.99      ( ~ r1_tarski(k10_relat_1(sK3,X0_53),X0_54)
% 3.01/0.99      | ~ v1_relat_1(sK3)
% 3.01/0.99      | k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53) ),
% 3.01/0.99      inference(subtyping,[status(esa)],[c_387]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1310,plain,
% 3.01/0.99      ( k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53)
% 3.01/0.99      | r1_tarski(k10_relat_1(sK3,X0_53),X0_54) != iProver_top
% 3.01/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1057,plain,
% 3.01/0.99      ( k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53)
% 3.01/0.99      | r1_tarski(k10_relat_1(sK3,X0_53),X0_54) != iProver_top
% 3.01/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1484,plain,
% 3.01/0.99      ( r1_tarski(k10_relat_1(sK3,X0_53),X0_54) != iProver_top
% 3.01/0.99      | k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_1310,c_37,c_1057,c_1417]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1485,plain,
% 3.01/0.99      ( k10_relat_1(k7_relat_1(sK3,X0_54),X0_53) = k10_relat_1(sK3,X0_53)
% 3.01/0.99      | r1_tarski(k10_relat_1(sK3,X0_53),X0_54) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_1484]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2189,plain,
% 3.01/0.99      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2087,c_1485]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7573,plain,
% 3.01/0.99      ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
% 3.01/0.99      inference(light_normalisation,[status(thm)],[c_7572,c_2189]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_7574,plain,
% 3.01/0.99      ( $false ),
% 3.01/0.99      inference(equality_resolution_simp,[status(thm)],[c_7573]) ).
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  ------                               Statistics
% 3.01/0.99  
% 3.01/0.99  ------ General
% 3.01/0.99  
% 3.01/0.99  abstr_ref_over_cycles:                  0
% 3.01/0.99  abstr_ref_under_cycles:                 0
% 3.01/0.99  gc_basic_clause_elim:                   0
% 3.01/0.99  forced_gc_time:                         0
% 3.01/0.99  parsing_time:                           0.009
% 3.01/0.99  unif_index_cands_time:                  0.
% 3.01/0.99  unif_index_add_time:                    0.
% 3.01/0.99  orderings_time:                         0.
% 3.01/0.99  out_proof_time:                         0.01
% 3.01/0.99  total_time:                             0.294
% 3.01/0.99  num_of_symbols:                         60
% 3.01/0.99  num_of_terms:                           8826
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing
% 3.01/0.99  
% 3.01/0.99  num_of_splits:                          0
% 3.01/0.99  num_of_split_atoms:                     0
% 3.01/0.99  num_of_reused_defs:                     0
% 3.01/0.99  num_eq_ax_congr_red:                    14
% 3.01/0.99  num_of_sem_filtered_clauses:            1
% 3.01/0.99  num_of_subtypes:                        4
% 3.01/0.99  monotx_restored_types:                  0
% 3.01/0.99  sat_num_of_epr_types:                   0
% 3.01/0.99  sat_num_of_non_cyclic_types:            0
% 3.01/0.99  sat_guarded_non_collapsed_types:        0
% 3.01/0.99  num_pure_diseq_elim:                    0
% 3.01/0.99  simp_replaced_by:                       0
% 3.01/0.99  res_preprocessed:                       110
% 3.01/0.99  prep_upred:                             0
% 3.01/0.99  prep_unflattend:                        25
% 3.01/0.99  smt_new_axioms:                         0
% 3.01/0.99  pred_elim_cands:                        3
% 3.01/0.99  pred_elim:                              7
% 3.01/0.99  pred_elim_cl:                           11
% 3.01/0.99  pred_elim_cycles:                       9
% 3.01/0.99  merged_defs:                            0
% 3.01/0.99  merged_defs_ncl:                        0
% 3.01/0.99  bin_hyper_res:                          0
% 3.01/0.99  prep_cycles:                            4
% 3.01/0.99  pred_elim_time:                         0.013
% 3.01/0.99  splitting_time:                         0.
% 3.01/0.99  sem_filter_time:                        0.
% 3.01/0.99  monotx_time:                            0.
% 3.01/0.99  subtype_inf_time:                       0.
% 3.01/0.99  
% 3.01/0.99  ------ Problem properties
% 3.01/0.99  
% 3.01/0.99  clauses:                                16
% 3.01/0.99  conjectures:                            4
% 3.01/0.99  epr:                                    1
% 3.01/0.99  horn:                                   16
% 3.01/0.99  ground:                                 6
% 3.01/0.99  unary:                                  5
% 3.01/0.99  binary:                                 7
% 3.01/0.99  lits:                                   32
% 3.01/0.99  lits_eq:                                7
% 3.01/0.99  fd_pure:                                0
% 3.01/0.99  fd_pseudo:                              0
% 3.01/0.99  fd_cond:                                0
% 3.01/0.99  fd_pseudo_cond:                         0
% 3.01/0.99  ac_symbols:                             0
% 3.01/0.99  
% 3.01/0.99  ------ Propositional Solver
% 3.01/0.99  
% 3.01/0.99  prop_solver_calls:                      30
% 3.01/0.99  prop_fast_solver_calls:                 881
% 3.01/0.99  smt_solver_calls:                       0
% 3.01/0.99  smt_fast_solver_calls:                  0
% 3.01/0.99  prop_num_of_clauses:                    2904
% 3.01/0.99  prop_preprocess_simplified:             6288
% 3.01/0.99  prop_fo_subsumed:                       27
% 3.01/0.99  prop_solver_time:                       0.
% 3.01/0.99  smt_solver_time:                        0.
% 3.01/0.99  smt_fast_solver_time:                   0.
% 3.01/0.99  prop_fast_solver_time:                  0.
% 3.01/0.99  prop_unsat_core_time:                   0.
% 3.01/0.99  
% 3.01/0.99  ------ QBF
% 3.01/0.99  
% 3.01/0.99  qbf_q_res:                              0
% 3.01/0.99  qbf_num_tautologies:                    0
% 3.01/0.99  qbf_prep_cycles:                        0
% 3.01/0.99  
% 3.01/0.99  ------ BMC1
% 3.01/0.99  
% 3.01/0.99  bmc1_current_bound:                     -1
% 3.01/0.99  bmc1_last_solved_bound:                 -1
% 3.01/0.99  bmc1_unsat_core_size:                   -1
% 3.01/0.99  bmc1_unsat_core_parents_size:           -1
% 3.01/0.99  bmc1_merge_next_fun:                    0
% 3.01/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation
% 3.01/0.99  
% 3.01/0.99  inst_num_of_clauses:                    776
% 3.01/0.99  inst_num_in_passive:                    165
% 3.01/0.99  inst_num_in_active:                     406
% 3.01/0.99  inst_num_in_unprocessed:                205
% 3.01/0.99  inst_num_of_loops:                      440
% 3.01/0.99  inst_num_of_learning_restarts:          0
% 3.01/0.99  inst_num_moves_active_passive:          30
% 3.01/0.99  inst_lit_activity:                      0
% 3.01/0.99  inst_lit_activity_moves:                0
% 3.01/0.99  inst_num_tautologies:                   0
% 3.01/0.99  inst_num_prop_implied:                  0
% 3.01/0.99  inst_num_existing_simplified:           0
% 3.01/0.99  inst_num_eq_res_simplified:             0
% 3.01/0.99  inst_num_child_elim:                    0
% 3.01/0.99  inst_num_of_dismatching_blockings:      550
% 3.01/0.99  inst_num_of_non_proper_insts:           854
% 3.01/0.99  inst_num_of_duplicates:                 0
% 3.01/0.99  inst_inst_num_from_inst_to_res:         0
% 3.01/0.99  inst_dismatching_checking_time:         0.
% 3.01/0.99  
% 3.01/0.99  ------ Resolution
% 3.01/0.99  
% 3.01/0.99  res_num_of_clauses:                     0
% 3.01/0.99  res_num_in_passive:                     0
% 3.01/0.99  res_num_in_active:                      0
% 3.01/0.99  res_num_of_loops:                       114
% 3.01/0.99  res_forward_subset_subsumed:            105
% 3.01/0.99  res_backward_subset_subsumed:           2
% 3.01/0.99  res_forward_subsumed:                   0
% 3.01/0.99  res_backward_subsumed:                  0
% 3.01/0.99  res_forward_subsumption_resolution:     0
% 3.01/0.99  res_backward_subsumption_resolution:    0
% 3.01/0.99  res_clause_to_clause_subsumption:       490
% 3.01/0.99  res_orphan_elimination:                 0
% 3.01/0.99  res_tautology_del:                      108
% 3.01/0.99  res_num_eq_res_simplified:              1
% 3.01/0.99  res_num_sel_changes:                    0
% 3.01/0.99  res_moves_from_active_to_pass:          0
% 3.01/0.99  
% 3.01/0.99  ------ Superposition
% 3.01/0.99  
% 3.01/0.99  sup_time_total:                         0.
% 3.01/0.99  sup_time_generating:                    0.
% 3.01/0.99  sup_time_sim_full:                      0.
% 3.01/0.99  sup_time_sim_immed:                     0.
% 3.01/0.99  
% 3.01/0.99  sup_num_of_clauses:                     140
% 3.01/0.99  sup_num_in_active:                      70
% 3.01/0.99  sup_num_in_passive:                     70
% 3.01/0.99  sup_num_of_loops:                       86
% 3.01/0.99  sup_fw_superposition:                   102
% 3.01/0.99  sup_bw_superposition:                   66
% 3.01/0.99  sup_immediate_simplified:               2
% 3.01/0.99  sup_given_eliminated:                   0
% 3.01/0.99  comparisons_done:                       0
% 3.01/0.99  comparisons_avoided:                    0
% 3.01/0.99  
% 3.01/0.99  ------ Simplifications
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  sim_fw_subset_subsumed:                 2
% 3.01/0.99  sim_bw_subset_subsumed:                 22
% 3.01/0.99  sim_fw_subsumed:                        0
% 3.01/0.99  sim_bw_subsumed:                        0
% 3.01/0.99  sim_fw_subsumption_res:                 1
% 3.01/0.99  sim_bw_subsumption_res:                 0
% 3.01/0.99  sim_tautology_del:                      2
% 3.01/0.99  sim_eq_tautology_del:                   0
% 3.01/0.99  sim_eq_res_simp:                        0
% 3.01/0.99  sim_fw_demodulated:                     1
% 3.01/0.99  sim_bw_demodulated:                     9
% 3.01/0.99  sim_light_normalised:                   1
% 3.01/0.99  sim_joinable_taut:                      0
% 3.01/0.99  sim_joinable_simp:                      0
% 3.01/0.99  sim_ac_normalised:                      0
% 3.01/0.99  sim_smt_subsumption:                    0
% 3.01/0.99  
%------------------------------------------------------------------------------
