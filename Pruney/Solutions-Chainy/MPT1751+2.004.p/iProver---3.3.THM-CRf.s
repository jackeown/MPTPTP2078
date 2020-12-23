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
% DateTime   : Thu Dec  3 12:22:31 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 378 expanded)
%              Number of clauses        :   91 ( 115 expanded)
%              Number of leaves         :   18 ( 130 expanded)
%              Depth                    :   25
%              Number of atoms          :  549 (3386 expanded)
%              Number of equality atoms :  129 ( 412 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & r1_tarski(X4,u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,sK4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4)
        & r1_tarski(sK4,u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
              & r1_tarski(X4,u1_struct_0(X2))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK3,X2),X4)
            & r1_tarski(X4,u1_struct_0(X2))
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                  & r1_tarski(X4,u1_struct_0(X2))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK2),X4)
                & r1_tarski(X4,u1_struct_0(sK2))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK1,X0,X3,X2),X4)
                    & r1_tarski(X4,u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & r1_tarski(X4,u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
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
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    & r1_tarski(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f39,f38,f37,f36,f35])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_972,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_53,X1_53)),k2_relat_1(X0_53))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_6145,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_53,X1_53)),k2_relat_1(X0_53)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_972])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_965,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_6152,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_2,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_292,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_7])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_964,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | r1_tarski(k2_relat_1(X0_53),X2_53) ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_6149,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(c_6891,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6152,c_6149])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_976,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | ~ r1_tarski(X2_53,X0_53)
    | r1_tarski(X2_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_6141,plain,
    ( r1_tarski(X0_53,X1_53) != iProver_top
    | r1_tarski(X2_53,X0_53) != iProver_top
    | r1_tarski(X2_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_976])).

cnf(c_6919,plain,
    ( r1_tarski(X0_53,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0_53,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6891,c_6141])).

cnf(c_6951,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_53)),u1_struct_0(sK0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6145,c_6919])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_971,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_6278,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_6279,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6278])).

cnf(c_6970,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_53)),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6951,c_37,c_6279])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_973,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_6144,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_969,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ r1_tarski(k1_relat_1(X0_53),X1_53)
    | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_6148,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
    | r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_969])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k7_relset_1(X1_53,X2_53,X0_53,X3_53) = k9_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_6147,plain,
    ( k7_relset_1(X0_53,X1_53,X2_53,X3_53) = k9_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_6681,plain,
    ( k7_relset_1(X0_53,X1_53,X2_53,X3_53) = k9_relat_1(X2_53,X3_53)
    | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
    | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_6148,c_6147])).

cnf(c_10032,plain,
    ( k7_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k9_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top
    | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6144,c_6681])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_975,plain,
    ( ~ v1_relat_1(X0_53)
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6142,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_975])).

cnf(c_17639,plain,
    ( k7_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k9_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10032,c_6142])).

cnf(c_17646,plain,
    ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(sK3,X0_53),X1_53) = k9_relat_1(k7_relat_1(sK3,X0_53),X1_53)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6970,c_17639])).

cnf(c_18265,plain,
    ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(sK3,X0_53),X1_53) = k9_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17646,c_37,c_6279])).

cnf(c_6669,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_53) = k9_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_6152,c_6147])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_385,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_963,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
    inference(subtyping,[status(esa)],[c_385])).

cnf(c_6150,plain,
    ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_963])).

cnf(c_6301,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_6152,c_6150])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f63])).

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
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

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
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_309,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_313,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_23,c_22,c_21])).

cnf(c_314,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_314])).

cnf(c_348,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_352,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_18])).

cnf(c_353,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_352])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_416,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_24])).

cnf(c_417,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_419,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_26,c_25,c_16])).

cnf(c_666,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_419])).

cnf(c_961,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_666])).

cnf(c_6319,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_6301,c_961])).

cnf(c_13,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_968,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_6478,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_6319,c_968])).

cnf(c_6710,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_6669,c_6478])).

cnf(c_18269,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_18265,c_6710])).

cnf(c_6146,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_6405,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6152,c_6146])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_967,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_6154,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_974,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | ~ v1_relat_1(X2_53)
    | k9_relat_1(k7_relat_1(X2_53,X1_53),X0_53) = k9_relat_1(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_6143,plain,
    ( k9_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k9_relat_1(X0_53,X2_53)
    | r1_tarski(X2_53,X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_974])).

cnf(c_6592,plain,
    ( k9_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),sK4) = k9_relat_1(X0_53,sK4)
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_6154,c_6143])).

cnf(c_6722,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_6405,c_6592])).

cnf(c_18270,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_18269,c_6722])).

cnf(c_18271,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_18270])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:40:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.57/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.57/1.48  
% 7.57/1.48  ------  iProver source info
% 7.57/1.48  
% 7.57/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.57/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.57/1.48  git: non_committed_changes: false
% 7.57/1.48  git: last_make_outside_of_git: false
% 7.57/1.48  
% 7.57/1.48  ------ 
% 7.57/1.48  ------ Parsing...
% 7.57/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.48  ------ Proving...
% 7.57/1.48  ------ Problem Properties 
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  clauses                                 16
% 7.57/1.48  conjectures                             4
% 7.57/1.48  EPR                                     1
% 7.57/1.48  Horn                                    16
% 7.57/1.48  unary                                   5
% 7.57/1.48  binary                                  7
% 7.57/1.48  lits                                    32
% 7.57/1.48  lits eq                                 7
% 7.57/1.49  fd_pure                                 0
% 7.57/1.49  fd_pseudo                               0
% 7.57/1.49  fd_cond                                 0
% 7.57/1.49  fd_pseudo_cond                          0
% 7.57/1.49  AC symbols                              0
% 7.57/1.49  
% 7.57/1.49  ------ Input Options Time Limit: Unbounded
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing...
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 7.57/1.49  Current options:
% 7.57/1.49  ------ 
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing...
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing...
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing...
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing...
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.49  
% 7.57/1.49  ------ Proving...
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  % SZS status Theorem for theBenchmark.p
% 7.57/1.49  
% 7.57/1.49   Resolution empty clause
% 7.57/1.49  
% 7.57/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.57/1.49  
% 7.57/1.49  fof(f6,axiom,(
% 7.57/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f22,plain,(
% 7.57/1.49    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.57/1.49    inference(ennf_transformation,[],[f6])).
% 7.57/1.49  
% 7.57/1.49  fof(f47,plain,(
% 7.57/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f22])).
% 7.57/1.49  
% 7.57/1.49  fof(f13,conjecture,(
% 7.57/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f14,negated_conjecture,(
% 7.57/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 7.57/1.49    inference(negated_conjecture,[],[f13])).
% 7.57/1.49  
% 7.57/1.49  fof(f32,plain,(
% 7.57/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.57/1.49    inference(ennf_transformation,[],[f14])).
% 7.57/1.49  
% 7.57/1.49  fof(f33,plain,(
% 7.57/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.57/1.49    inference(flattening,[],[f32])).
% 7.57/1.49  
% 7.57/1.49  fof(f39,plain,(
% 7.57/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,sK4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4) & r1_tarski(sK4,u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.57/1.49    introduced(choice_axiom,[])).
% 7.57/1.49  
% 7.57/1.49  fof(f38,plain,(
% 7.57/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.57/1.49    introduced(choice_axiom,[])).
% 7.57/1.49  
% 7.57/1.49  fof(f37,plain,(
% 7.57/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK2),X4) & r1_tarski(X4,u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 7.57/1.49    introduced(choice_axiom,[])).
% 7.57/1.49  
% 7.57/1.49  fof(f36,plain,(
% 7.57/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.57/1.49    introduced(choice_axiom,[])).
% 7.57/1.49  
% 7.57/1.49  fof(f35,plain,(
% 7.57/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.57/1.49    introduced(choice_axiom,[])).
% 7.57/1.49  
% 7.57/1.49  fof(f40,plain,(
% 7.57/1.49    ((((k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & r1_tarski(sK4,u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.57/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f39,f38,f37,f36,f35])).
% 7.57/1.49  
% 7.57/1.49  fof(f64,plain,(
% 7.57/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f2,axiom,(
% 7.57/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f18,plain,(
% 7.57/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.57/1.49    inference(ennf_transformation,[],[f2])).
% 7.57/1.49  
% 7.57/1.49  fof(f34,plain,(
% 7.57/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.57/1.49    inference(nnf_transformation,[],[f18])).
% 7.57/1.49  
% 7.57/1.49  fof(f42,plain,(
% 7.57/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f34])).
% 7.57/1.49  
% 7.57/1.49  fof(f8,axiom,(
% 7.57/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f15,plain,(
% 7.57/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.57/1.49    inference(pure_predicate_removal,[],[f8])).
% 7.57/1.49  
% 7.57/1.49  fof(f24,plain,(
% 7.57/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.49    inference(ennf_transformation,[],[f15])).
% 7.57/1.49  
% 7.57/1.49  fof(f49,plain,(
% 7.57/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.49    inference(cnf_transformation,[],[f24])).
% 7.57/1.49  
% 7.57/1.49  fof(f7,axiom,(
% 7.57/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f23,plain,(
% 7.57/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.49    inference(ennf_transformation,[],[f7])).
% 7.57/1.49  
% 7.57/1.49  fof(f48,plain,(
% 7.57/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.49    inference(cnf_transformation,[],[f23])).
% 7.57/1.49  
% 7.57/1.49  fof(f1,axiom,(
% 7.57/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f16,plain,(
% 7.57/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.57/1.49    inference(ennf_transformation,[],[f1])).
% 7.57/1.49  
% 7.57/1.49  fof(f17,plain,(
% 7.57/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.57/1.49    inference(flattening,[],[f16])).
% 7.57/1.49  
% 7.57/1.49  fof(f41,plain,(
% 7.57/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f17])).
% 7.57/1.49  
% 7.57/1.49  fof(f5,axiom,(
% 7.57/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f21,plain,(
% 7.57/1.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.57/1.49    inference(ennf_transformation,[],[f5])).
% 7.57/1.49  
% 7.57/1.49  fof(f46,plain,(
% 7.57/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f21])).
% 7.57/1.49  
% 7.57/1.49  fof(f10,axiom,(
% 7.57/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f26,plain,(
% 7.57/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.57/1.49    inference(ennf_transformation,[],[f10])).
% 7.57/1.49  
% 7.57/1.49  fof(f27,plain,(
% 7.57/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.57/1.49    inference(flattening,[],[f26])).
% 7.57/1.49  
% 7.57/1.49  fof(f51,plain,(
% 7.57/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f27])).
% 7.57/1.49  
% 7.57/1.49  fof(f9,axiom,(
% 7.57/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f25,plain,(
% 7.57/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.49    inference(ennf_transformation,[],[f9])).
% 7.57/1.49  
% 7.57/1.49  fof(f50,plain,(
% 7.57/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.49    inference(cnf_transformation,[],[f25])).
% 7.57/1.49  
% 7.57/1.49  fof(f3,axiom,(
% 7.57/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f19,plain,(
% 7.57/1.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.57/1.49    inference(ennf_transformation,[],[f3])).
% 7.57/1.49  
% 7.57/1.49  fof(f44,plain,(
% 7.57/1.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f19])).
% 7.57/1.49  
% 7.57/1.49  fof(f11,axiom,(
% 7.57/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f28,plain,(
% 7.57/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.57/1.49    inference(ennf_transformation,[],[f11])).
% 7.57/1.49  
% 7.57/1.49  fof(f29,plain,(
% 7.57/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.57/1.49    inference(flattening,[],[f28])).
% 7.57/1.49  
% 7.57/1.49  fof(f52,plain,(
% 7.57/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f29])).
% 7.57/1.49  
% 7.57/1.49  fof(f62,plain,(
% 7.57/1.49    v1_funct_1(sK3)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f63,plain,(
% 7.57/1.49    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f12,axiom,(
% 7.57/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f30,plain,(
% 7.57/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.57/1.49    inference(ennf_transformation,[],[f12])).
% 7.57/1.49  
% 7.57/1.49  fof(f31,plain,(
% 7.57/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.57/1.49    inference(flattening,[],[f30])).
% 7.57/1.49  
% 7.57/1.49  fof(f53,plain,(
% 7.57/1.49    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f31])).
% 7.57/1.49  
% 7.57/1.49  fof(f61,plain,(
% 7.57/1.49    m1_pre_topc(sK2,sK1)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f57,plain,(
% 7.57/1.49    ~v2_struct_0(sK1)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f58,plain,(
% 7.57/1.49    v2_pre_topc(sK1)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f59,plain,(
% 7.57/1.49    l1_pre_topc(sK1)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f56,plain,(
% 7.57/1.49    l1_pre_topc(sK0)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f54,plain,(
% 7.57/1.49    ~v2_struct_0(sK0)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f55,plain,(
% 7.57/1.49    v2_pre_topc(sK0)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f67,plain,(
% 7.57/1.49    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f66,plain,(
% 7.57/1.49    r1_tarski(sK4,u1_struct_0(sK2))),
% 7.57/1.49    inference(cnf_transformation,[],[f40])).
% 7.57/1.49  
% 7.57/1.49  fof(f4,axiom,(
% 7.57/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 7.57/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.49  
% 7.57/1.49  fof(f20,plain,(
% 7.57/1.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 7.57/1.49    inference(ennf_transformation,[],[f4])).
% 7.57/1.49  
% 7.57/1.49  fof(f45,plain,(
% 7.57/1.49    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 7.57/1.49    inference(cnf_transformation,[],[f20])).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6,plain,
% 7.57/1.49      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 7.57/1.49      | ~ v1_relat_1(X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_972,plain,
% 7.57/1.49      ( r1_tarski(k2_relat_1(k7_relat_1(X0_53,X1_53)),k2_relat_1(X0_53))
% 7.57/1.49      | ~ v1_relat_1(X0_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6145,plain,
% 7.57/1.49      ( r1_tarski(k2_relat_1(k7_relat_1(X0_53,X1_53)),k2_relat_1(X0_53)) = iProver_top
% 7.57/1.49      | v1_relat_1(X0_53) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_972]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_16,negated_conjecture,
% 7.57/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 7.57/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_965,negated_conjecture,
% 7.57/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6152,plain,
% 7.57/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_2,plain,
% 7.57/1.49      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_8,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 7.57/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_287,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.49      | r1_tarski(k2_relat_1(X3),X4)
% 7.57/1.49      | ~ v1_relat_1(X3)
% 7.57/1.49      | X0 != X3
% 7.57/1.49      | X2 != X4 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_288,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.49      | r1_tarski(k2_relat_1(X0),X2)
% 7.57/1.49      | ~ v1_relat_1(X0) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_287]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_7,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_292,plain,
% 7.57/1.49      ( r1_tarski(k2_relat_1(X0),X2)
% 7.57/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.57/1.49      inference(global_propositional_subsumption,[status(thm)],[c_288,c_7]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_293,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.49      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.57/1.49      inference(renaming,[status(thm)],[c_292]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_964,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.57/1.49      | r1_tarski(k2_relat_1(X0_53),X2_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_293]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6149,plain,
% 7.57/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_relat_1(X0_53),X2_53) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_964]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6891,plain,
% 7.57/1.49      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6152,c_6149]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_0,plain,
% 7.57/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.57/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_976,plain,
% 7.57/1.49      ( ~ r1_tarski(X0_53,X1_53)
% 7.57/1.49      | ~ r1_tarski(X2_53,X0_53)
% 7.57/1.49      | r1_tarski(X2_53,X1_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6141,plain,
% 7.57/1.49      ( r1_tarski(X0_53,X1_53) != iProver_top
% 7.57/1.49      | r1_tarski(X2_53,X0_53) != iProver_top
% 7.57/1.49      | r1_tarski(X2_53,X1_53) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_976]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6919,plain,
% 7.57/1.49      ( r1_tarski(X0_53,u1_struct_0(sK0)) = iProver_top
% 7.57/1.49      | r1_tarski(X0_53,k2_relat_1(sK3)) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6891,c_6141]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6951,plain,
% 7.57/1.49      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_53)),u1_struct_0(sK0)) = iProver_top
% 7.57/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6145,c_6919]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_37,plain,
% 7.57/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_971,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.57/1.49      | v1_relat_1(X0_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6278,plain,
% 7.57/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.57/1.49      | v1_relat_1(sK3) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_971]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6279,plain,
% 7.57/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 7.57/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_6278]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6970,plain,
% 7.57/1.49      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0_53)),u1_struct_0(sK0)) = iProver_top ),
% 7.57/1.49      inference(global_propositional_subsumption,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_6951,c_37,c_6279]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_5,plain,
% 7.57/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_973,plain,
% 7.57/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
% 7.57/1.49      | ~ v1_relat_1(X0_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6144,plain,
% 7.57/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
% 7.57/1.49      | v1_relat_1(X0_53) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_10,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.57/1.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.57/1.49      | ~ v1_relat_1(X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_969,plain,
% 7.57/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.57/1.49      | ~ r1_tarski(k1_relat_1(X0_53),X1_53)
% 7.57/1.49      | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
% 7.57/1.49      | ~ v1_relat_1(X0_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6148,plain,
% 7.57/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
% 7.57/1.49      | r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
% 7.57/1.49      | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
% 7.57/1.49      | v1_relat_1(X0_53) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_969]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_9,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.57/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_970,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.57/1.49      | k7_relset_1(X1_53,X2_53,X0_53,X3_53) = k9_relat_1(X0_53,X3_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6147,plain,
% 7.57/1.49      ( k7_relset_1(X0_53,X1_53,X2_53,X3_53) = k9_relat_1(X2_53,X3_53)
% 7.57/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6681,plain,
% 7.57/1.49      ( k7_relset_1(X0_53,X1_53,X2_53,X3_53) = k9_relat_1(X2_53,X3_53)
% 7.57/1.49      | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
% 7.57/1.49      | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
% 7.57/1.49      | v1_relat_1(X2_53) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6148,c_6147]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_10032,plain,
% 7.57/1.49      ( k7_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k9_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 7.57/1.49      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 7.57/1.49      | v1_relat_1(X2_53) != iProver_top
% 7.57/1.49      | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6144,c_6681]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3,plain,
% 7.57/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.57/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_975,plain,
% 7.57/1.49      ( ~ v1_relat_1(X0_53) | v1_relat_1(k7_relat_1(X0_53,X1_53)) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6142,plain,
% 7.57/1.49      ( v1_relat_1(X0_53) != iProver_top
% 7.57/1.49      | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_975]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_17639,plain,
% 7.57/1.49      ( k7_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k9_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 7.57/1.49      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 7.57/1.49      | v1_relat_1(X2_53) != iProver_top ),
% 7.57/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_10032,c_6142]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_17646,plain,
% 7.57/1.49      ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(sK3,X0_53),X1_53) = k9_relat_1(k7_relat_1(sK3,X0_53),X1_53)
% 7.57/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6970,c_17639]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_18265,plain,
% 7.57/1.49      ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(sK3,X0_53),X1_53) = k9_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
% 7.57/1.49      inference(global_propositional_subsumption,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_17646,c_37,c_6279]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6669,plain,
% 7.57/1.49      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_53) = k9_relat_1(sK3,X0_53) ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6152,c_6147]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_11,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.49      | ~ v1_funct_1(X0)
% 7.57/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.57/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_18,negated_conjecture,
% 7.57/1.49      ( v1_funct_1(sK3) ),
% 7.57/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_384,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 7.57/1.49      | sK3 != X0 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_385,plain,
% 7.57/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.57/1.49      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_384]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_963,plain,
% 7.57/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.57/1.49      | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_385]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6150,plain,
% 7.57/1.49      ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
% 7.57/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_963]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6301,plain,
% 7.57/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6152,c_6150]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_17,negated_conjecture,
% 7.57/1.49      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 7.57/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_12,plain,
% 7.57/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.57/1.49      | ~ m1_pre_topc(X3,X1)
% 7.57/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.57/1.49      | v2_struct_0(X1)
% 7.57/1.49      | v2_struct_0(X2)
% 7.57/1.49      | ~ v2_pre_topc(X2)
% 7.57/1.49      | ~ v2_pre_topc(X1)
% 7.57/1.49      | ~ l1_pre_topc(X2)
% 7.57/1.49      | ~ l1_pre_topc(X1)
% 7.57/1.49      | ~ v1_funct_1(X0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.57/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_19,negated_conjecture,
% 7.57/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.57/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_308,plain,
% 7.57/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.57/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.57/1.49      | v2_struct_0(X2)
% 7.57/1.49      | v2_struct_0(X1)
% 7.57/1.49      | ~ v2_pre_topc(X2)
% 7.57/1.49      | ~ v2_pre_topc(X1)
% 7.57/1.49      | ~ l1_pre_topc(X2)
% 7.57/1.49      | ~ l1_pre_topc(X1)
% 7.57/1.49      | ~ v1_funct_1(X0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 7.57/1.49      | sK2 != X3
% 7.57/1.49      | sK1 != X1 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_309,plain,
% 7.57/1.49      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.57/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.57/1.49      | v2_struct_0(X1)
% 7.57/1.49      | v2_struct_0(sK1)
% 7.57/1.49      | ~ v2_pre_topc(X1)
% 7.57/1.49      | ~ v2_pre_topc(sK1)
% 7.57/1.49      | ~ l1_pre_topc(X1)
% 7.57/1.49      | ~ l1_pre_topc(sK1)
% 7.57/1.49      | ~ v1_funct_1(X0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_308]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_23,negated_conjecture,
% 7.57/1.49      ( ~ v2_struct_0(sK1) ),
% 7.57/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_22,negated_conjecture,
% 7.57/1.49      ( v2_pre_topc(sK1) ),
% 7.57/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_21,negated_conjecture,
% 7.57/1.49      ( l1_pre_topc(sK1) ),
% 7.57/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_313,plain,
% 7.57/1.49      ( ~ l1_pre_topc(X1)
% 7.57/1.49      | v2_struct_0(X1)
% 7.57/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.57/1.49      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.57/1.49      | ~ v2_pre_topc(X1)
% 7.57/1.49      | ~ v1_funct_1(X0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 7.57/1.49      inference(global_propositional_subsumption,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_309,c_23,c_22,c_21]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_314,plain,
% 7.57/1.49      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.57/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.57/1.49      | v2_struct_0(X1)
% 7.57/1.49      | ~ v2_pre_topc(X1)
% 7.57/1.49      | ~ l1_pre_topc(X1)
% 7.57/1.49      | ~ v1_funct_1(X0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 7.57/1.49      inference(renaming,[status(thm)],[c_313]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_347,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.57/1.49      | v2_struct_0(X1)
% 7.57/1.49      | ~ v2_pre_topc(X1)
% 7.57/1.49      | ~ l1_pre_topc(X1)
% 7.57/1.49      | ~ v1_funct_1(X0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
% 7.57/1.49      | u1_struct_0(X1) != u1_struct_0(sK0)
% 7.57/1.49      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 7.57/1.49      | sK3 != X0 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_314]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_348,plain,
% 7.57/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 7.57/1.49      | v2_struct_0(X0)
% 7.57/1.49      | ~ v2_pre_topc(X0)
% 7.57/1.49      | ~ l1_pre_topc(X0)
% 7.57/1.49      | ~ v1_funct_1(sK3)
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
% 7.57/1.49      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_347]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_352,plain,
% 7.57/1.49      ( ~ l1_pre_topc(X0)
% 7.57/1.49      | ~ v2_pre_topc(X0)
% 7.57/1.49      | v2_struct_0(X0)
% 7.57/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
% 7.57/1.49      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 7.57/1.49      inference(global_propositional_subsumption,[status(thm)],[c_348,c_18]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_353,plain,
% 7.57/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 7.57/1.49      | v2_struct_0(X0)
% 7.57/1.49      | ~ v2_pre_topc(X0)
% 7.57/1.49      | ~ l1_pre_topc(X0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
% 7.57/1.49      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 7.57/1.49      inference(renaming,[status(thm)],[c_352]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_24,negated_conjecture,
% 7.57/1.49      ( l1_pre_topc(sK0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_416,plain,
% 7.57/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 7.57/1.49      | v2_struct_0(X0)
% 7.57/1.49      | ~ v2_pre_topc(X0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
% 7.57/1.49      | u1_struct_0(X0) != u1_struct_0(sK0)
% 7.57/1.49      | sK0 != X0 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_353,c_24]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_417,plain,
% 7.57/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.57/1.49      | v2_struct_0(sK0)
% 7.57/1.49      | ~ v2_pre_topc(sK0)
% 7.57/1.49      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
% 7.57/1.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_416]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_26,negated_conjecture,
% 7.57/1.49      ( ~ v2_struct_0(sK0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_25,negated_conjecture,
% 7.57/1.49      ( v2_pre_topc(sK0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_419,plain,
% 7.57/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
% 7.57/1.49      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 7.57/1.49      inference(global_propositional_subsumption,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_417,c_26,c_25,c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_666,plain,
% 7.57/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.57/1.49      inference(equality_resolution_simp,[status(thm)],[c_419]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_961,plain,
% 7.57/1.49      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_666]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6319,plain,
% 7.57/1.49      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 7.57/1.49      inference(demodulation,[status(thm)],[c_6301,c_961]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_13,negated_conjecture,
% 7.57/1.49      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
% 7.57/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_968,negated_conjecture,
% 7.57/1.49      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6478,plain,
% 7.57/1.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) ),
% 7.57/1.49      inference(demodulation,[status(thm)],[c_6319,c_968]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6710,plain,
% 7.57/1.49      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
% 7.57/1.49      inference(demodulation,[status(thm)],[c_6669,c_6478]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_18269,plain,
% 7.57/1.49      ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
% 7.57/1.49      inference(demodulation,[status(thm)],[c_18265,c_6710]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6146,plain,
% 7.57/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.57/1.49      | v1_relat_1(X0_53) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_971]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6405,plain,
% 7.57/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6152,c_6146]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_14,negated_conjecture,
% 7.57/1.49      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 7.57/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_967,negated_conjecture,
% 7.57/1.49      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6154,plain,
% 7.57/1.49      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_4,plain,
% 7.57/1.49      ( ~ r1_tarski(X0,X1)
% 7.57/1.49      | ~ v1_relat_1(X2)
% 7.57/1.49      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_974,plain,
% 7.57/1.49      ( ~ r1_tarski(X0_53,X1_53)
% 7.57/1.49      | ~ v1_relat_1(X2_53)
% 7.57/1.49      | k9_relat_1(k7_relat_1(X2_53,X1_53),X0_53) = k9_relat_1(X2_53,X0_53) ),
% 7.57/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6143,plain,
% 7.57/1.49      ( k9_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k9_relat_1(X0_53,X2_53)
% 7.57/1.49      | r1_tarski(X2_53,X1_53) != iProver_top
% 7.57/1.49      | v1_relat_1(X0_53) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_974]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6592,plain,
% 7.57/1.49      ( k9_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),sK4) = k9_relat_1(X0_53,sK4)
% 7.57/1.49      | v1_relat_1(X0_53) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6154,c_6143]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6722,plain,
% 7.57/1.49      ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_6405,c_6592]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_18270,plain,
% 7.57/1.49      ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) ),
% 7.57/1.49      inference(light_normalisation,[status(thm)],[c_18269,c_6722]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_18271,plain,
% 7.57/1.49      ( $false ),
% 7.57/1.49      inference(equality_resolution_simp,[status(thm)],[c_18270]) ).
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.57/1.49  
% 7.57/1.49  ------                               Statistics
% 7.57/1.49  
% 7.57/1.49  ------ Selected
% 7.57/1.49  
% 7.57/1.49  total_time:                             0.569
% 7.57/1.49  
%------------------------------------------------------------------------------
