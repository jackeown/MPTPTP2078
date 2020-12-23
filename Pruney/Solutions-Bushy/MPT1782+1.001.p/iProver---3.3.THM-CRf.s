%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1782+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:23 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 517 expanded)
%              Number of clauses        :  117 ( 170 expanded)
%              Number of leaves         :   23 ( 169 expanded)
%              Depth                    :   14
%              Number of atoms          :  710 (4055 expanded)
%              Number of equality atoms :  163 ( 204 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

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
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3)) ) ) ) ) ),
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
                   => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
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

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,sK2),X3))
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
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
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
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k4_tmap_1(X0,X2),X3))
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
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X0,X2),X3))
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
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),k1_partfun1(u1_struct_0(X2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k4_tmap_1(sK0,X2),X3))
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
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f43,f42,f41,f40])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                            & v1_funct_1(X5) )
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1079,plain,
    ( ~ m1_subset_1(X0_54,X0_56)
    | m1_subset_1(X1_54,X0_56)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_2366,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | X1_54 != X0_54 ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_3743,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | X1_54 != X0_54 ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_7209,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) != X0_54 ),
    inference(instantiation,[status(thm)],[c_3743])).

cnf(c_8601,plain,
    ( m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k5_relat_1(k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) != k5_relat_1(k3_struct_0(sK0),sK3) ),
    inference(instantiation,[status(thm)],[c_7209])).

cnf(c_1084,plain,
    ( ~ r2_relset_1(X0_53,X1_53,X0_54,X1_54)
    | r2_relset_1(X0_53,X1_53,X2_54,X1_54)
    | X2_54 != X0_54 ),
    theory(equality)).

cnf(c_6829,plain,
    ( ~ r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_54,sK3)
    | r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK3)
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) != X0_54 ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(c_8092,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK3)
    | ~ r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k3_struct_0(sK0),sK3),sK3)
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) != k5_relat_1(k3_struct_0(sK0),sK3) ),
    inference(instantiation,[status(thm)],[c_6829])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1067,plain,
    ( ~ r2_relset_1(X0_53,X1_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | X1_54 = X0_54 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2835,plain,
    ( ~ r2_relset_1(X0_53,X1_53,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK3)
    | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | sK3 = k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) ),
    inference(instantiation,[status(thm)],[c_1067])).

cnf(c_5047,plain,
    ( ~ r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK3)
    | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK3 = k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) ),
    inference(instantiation,[status(thm)],[c_2835])).

cnf(c_1076,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_4713,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3) = k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_1085,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_54,X1_54)
    | r2_funct_2(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_1632,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,X1_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != X1_54
    | k2_tmap_1(sK0,sK1,sK3,sK2) != X0_54 ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_1666,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X0_54,sK2),X1_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != X1_54
    | k2_tmap_1(sK0,sK1,sK3,sK2) != k2_tmap_1(sK0,sK1,X0_54,sK2) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_1795,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X0_54,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1_54,X2_54))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X1_54,X2_54)
    | k2_tmap_1(sK0,sK1,sK3,sK2) != k2_tmap_1(sK0,sK1,X0_54,sK2) ),
    inference(instantiation,[status(thm)],[c_1666])).

cnf(c_4697,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X0_54,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),X1_54))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),X1_54)
    | k2_tmap_1(sK0,sK1,sK3,sK2) != k2_tmap_1(sK0,sK1,X0_54,sK2) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_4699,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3)
    | k2_tmap_1(sK0,sK1,sK3,sK2) != k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_4697])).

cnf(c_2285,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,X1_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X2_54,sK2),X3_54)
    | X3_54 != X1_54
    | k2_tmap_1(sK0,sK1,X2_54,sK2) != X0_54 ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_3371,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X0_54,sK2),X1_54)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3))
    | X1_54 != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3)
    | k2_tmap_1(sK0,sK1,X0_54,sK2) != k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_3892,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X0_54,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3))
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3)
    | k2_tmap_1(sK0,sK1,X0_54,sK2) != k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3371])).

cnf(c_3894,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3))
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3)
    | k2_tmap_1(sK0,sK1,sK3,sK2) != k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_3892])).

cnf(c_1077,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_1794,plain,
    ( X0_54 != X1_54
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != X1_54
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = X0_54 ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_1889,plain,
    ( X0_54 != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = X0_54
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_2076,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X0_54,X1_54) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X0_54,X1_54)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1889])).

cnf(c_3885,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),X0_54) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),X0_54)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_3886,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3)
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) != k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_3885])).

cnf(c_1083,plain,
    ( X0_54 != X1_54
    | X2_54 != X3_54
    | k1_partfun1(X0_53,X1_53,X2_53,X3_53,X0_54,X2_54) = k1_partfun1(X0_53,X1_53,X2_53,X3_53,X1_54,X3_54) ),
    theory(equality)).

cnf(c_2459,plain,
    ( X0_54 != k4_tmap_1(sK0,sK2)
    | X1_54 != sK3
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),X0_54,X1_54) = k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_3567,plain,
    ( X0_54 != sK3
    | k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),X0_54) = k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2) != k4_tmap_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_2459])).

cnf(c_3568,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3) = k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2) != k4_tmap_1(sK0,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3567])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1056,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1573,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | k6_partfun1(u1_struct_0(X0)) = k3_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_382,plain,
    ( ~ l1_pre_topc(X0)
    | k6_partfun1(u1_struct_0(X0)) = k3_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_0])).

cnf(c_1049,plain,
    ( ~ l1_pre_topc(X0_55)
    | k6_partfun1(u1_struct_0(X0_55)) = k3_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_1580,plain,
    ( k6_partfun1(u1_struct_0(X0_55)) = k3_struct_0(X0_55)
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_2268,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k3_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1573,c_1580])).

cnf(c_6,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1073,plain,
    ( m1_subset_1(k6_partfun1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1556,plain,
    ( m1_subset_1(k6_partfun1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1073])).

cnf(c_2692,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_1556])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1063,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1566,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1069,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | k4_relset_1(X2_53,X3_53,X0_53,X1_53,X1_54,X0_54) = k5_relat_1(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1560,plain,
    ( k4_relset_1(X0_53,X1_53,X2_53,X3_53,X0_54,X1_54) = k5_relat_1(X0_54,X1_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1069])).

cnf(c_2610,plain,
    ( k4_relset_1(X0_53,X1_53,u1_struct_0(sK0),u1_struct_0(sK1),X0_54,sK3) = k5_relat_1(X0_54,sK3)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_1560])).

cnf(c_2913,plain,
    ( k4_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = k5_relat_1(k3_struct_0(sK0),sK3) ),
    inference(superposition,[status(thm)],[c_2692,c_2610])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1074,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | m1_subset_1(k4_relset_1(X2_53,X3_53,X0_53,X1_53,X1_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1555,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(k4_relset_1(X0_53,X1_53,X2_53,X3_53,X0_54,X1_54),k1_zfmisc_1(k2_zfmisc_1(X0_53,X3_53))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_3439,plain,
    ( m1_subset_1(k5_relat_1(k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_1555])).

cnf(c_3440,plain,
    ( m1_subset_1(k5_relat_1(k3_struct_0(sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3439])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1070,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | ~ v1_funct_1(X1_54)
    | ~ v1_funct_1(X0_54)
    | k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_54,X0_54) = k5_relat_1(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1559,plain,
    ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X0_54,X1_54) = k5_relat_1(X0_54,X1_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_3006,plain,
    ( k1_partfun1(X0_53,X1_53,u1_struct_0(sK0),u1_struct_0(sK1),X0_54,sK3) = k5_relat_1(X0_54,sK3)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_1559])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3165,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k1_partfun1(X0_53,X1_53,u1_struct_0(sK0),u1_struct_0(sK1),X0_54,sK3) = k5_relat_1(X0_54,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3006,c_38])).

cnf(c_3166,plain,
    ( k1_partfun1(X0_53,X1_53,u1_struct_0(sK0),u1_struct_0(sK1),X0_54,sK3) = k5_relat_1(X0_54,sK3)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3165])).

cnf(c_3170,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) = k5_relat_1(k3_struct_0(sK0),sK3)
    | v1_funct_1(k3_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2692,c_3166])).

cnf(c_2704,plain,
    ( k4_relset_1(X0_53,X0_53,u1_struct_0(sK0),u1_struct_0(sK1),k6_partfun1(X0_53),sK3) = k5_relat_1(k6_partfun1(X0_53),sK3) ),
    inference(superposition,[status(thm)],[c_1556,c_2610])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1065,plain,
    ( r2_relset_1(X0_53,X1_53,k4_relset_1(X0_53,X0_53,X0_53,X1_53,k6_partfun1(X0_53),X0_54),X0_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1564,plain,
    ( r2_relset_1(X0_53,X1_53,k4_relset_1(X0_53,X0_53,X0_53,X1_53,k6_partfun1(X0_53),X0_54),X0_54) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(c_3155,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k6_partfun1(u1_struct_0(sK0)),sK3),sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2704,c_1564])).

cnf(c_3157,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k3_struct_0(sK0),sK3),sK3) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3155,c_2268])).

cnf(c_3163,plain,
    ( r2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k5_relat_1(k3_struct_0(sK0),sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3157])).

cnf(c_1078,plain,
    ( X0_54 != X1_54
    | k2_tmap_1(X0_55,X1_55,X0_54,X2_55) = k2_tmap_1(X0_55,X1_55,X1_54,X2_55) ),
    theory(equality)).

cnf(c_1708,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k2_tmap_1(sK0,sK1,X0_54,sK2)
    | sK3 != X0_54 ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_2653,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2)
    | sK3 != k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_1874,plain,
    ( k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) = k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_17,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X0),k1_partfun1(u1_struct_0(X0),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X3,X4,X0),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_586,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X0),k1_partfun1(u1_struct_0(X0),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X3,X4,X0),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | sK0 != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_587,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(sK0,X0,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,X3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK0,X1,X2,sK2),X3))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_591,plain,
    ( ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(sK0,X0,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,X3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK0,X1,X2,sK2),X3))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_29,c_28,c_27,c_23])).

cnf(c_592,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(sK0,X0,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,X3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK0,X1,X2,sK2),X3))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_591])).

cnf(c_1047,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k2_tmap_1(sK0,X0_55,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1_55),u1_struct_0(X1_55),u1_struct_0(X0_55),X0_54,X1_54),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(X1_55),u1_struct_0(X1_55),u1_struct_0(X0_55),k2_tmap_1(sK0,X1_55,X0_54,sK2),X1_54))
    | ~ v1_funct_2(X1_54,u1_struct_0(X1_55),u1_struct_0(X0_55))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X1_55))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1_55))))
    | ~ v1_funct_1(X1_54)
    | ~ v1_funct_1(X0_54)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_592])).

cnf(c_1642,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0_55),k2_tmap_1(sK0,X0_55,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X0_55),k3_struct_0(sK0),X0_54),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X0_55),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),X0_54))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(X0_55))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | v2_struct_0(X0_55)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_1747,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k3_struct_0(sK0),sK3),sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2),sK3))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_1697,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,X1,k3_struct_0(X1),X0) = k4_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_578,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
    | sK0 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_579,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2) = k4_tmap_1(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_581,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2) = k4_tmap_1(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_29,c_28,c_27])).

cnf(c_1048,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK2) = k4_tmap_1(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_581])).

cnf(c_1095,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_2,plain,
    ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_88,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_85,plain,
    ( v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( v1_funct_1(k3_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_81,plain,
    ( v1_funct_1(k3_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_83,plain,
    ( v1_funct_1(k3_struct_0(sK0)) = iProver_top
    | l1_struct_0(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_81])).

cnf(c_82,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_72,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_74,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_struct_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_18,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k4_tmap_1(sK0,sK2),sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8601,c_8092,c_5047,c_4713,c_4699,c_3894,c_3886,c_3568,c_3440,c_3170,c_3163,c_2653,c_1874,c_1747,c_1697,c_1048,c_1095,c_88,c_85,c_83,c_82,c_74,c_73,c_18,c_19,c_20,c_21,c_24,c_25,c_26,c_32,c_27,c_28,c_29])).


%------------------------------------------------------------------------------
