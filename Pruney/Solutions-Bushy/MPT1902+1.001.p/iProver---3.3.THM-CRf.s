%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1902+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:50 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  257 (1683 expanded)
%              Number of clauses        :  187 ( 538 expanded)
%              Number of leaves         :   23 ( 454 expanded)
%              Depth                    :   30
%              Number of atoms          : 1035 (12124 expanded)
%              Number of equality atoms :  436 ( 989 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_tdlat_3(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_tdlat_3(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_tdlat_3(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_tdlat_3(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_tdlat_3(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_pre_topc(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v5_pre_topc(sK4,X0,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_tdlat_3(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ~ v5_pre_topc(X2,X0,sK3)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_tdlat_3(sK3)
        & v2_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_tdlat_3(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_tdlat_3(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f45,f44,f43])).

fof(f74,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
                    & v4_pre_topc(sK0(X0,X1,X2),X1)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( u1_struct_0(X0) != X1
                & k1_xboole_0 != X1
                & v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( u1_struct_0(X0) = X1
              | k1_xboole_0 = X1
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != X1
          & k1_xboole_0 != X1
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_struct_0(X0) != sK1(X0)
        & k1_xboole_0 != sK1(X0)
        & v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ( u1_struct_0(X0) != sK1(X0)
            & k1_xboole_0 != sK1(X0)
            & v4_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f61,plain,(
    ! [X2,X0] :
      ( u1_struct_0(X0) = X2
      | k1_xboole_0 = X2
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | v4_pre_topc(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1802,plain,
    ( X0_51 != X1_51
    | k10_relat_1(X2_51,X0_51) = k10_relat_1(X2_51,X1_51) ),
    theory(equality)).

cnf(c_3954,plain,
    ( X0_51 != X1_51
    | k10_relat_1(sK4,X0_51) = k10_relat_1(sK4,X1_51) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_7595,plain,
    ( X0_51 != sK0(sK2,sK3,sK4)
    | k10_relat_1(sK4,X0_51) = k10_relat_1(sK4,sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3954])).

cnf(c_7597,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k10_relat_1(sK4,sK0(sK2,sK3,sK4))
    | k1_xboole_0 != sK0(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_7595])).

cnf(c_1793,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_3794,plain,
    ( X0_51 != X1_51
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X2_51) != X1_51
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X2_51) = X0_51 ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_4271,plain,
    ( X0_51 != k10_relat_1(sK4,X1_51)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51) = X0_51
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51) != k10_relat_1(sK4,X1_51) ),
    inference(instantiation,[status(thm)],[c_3794])).

cnf(c_4665,plain,
    ( X0_51 != k10_relat_1(sK4,sK0(sK2,sK3,sK4))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = X0_51
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k10_relat_1(sK4,sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4271])).

cnf(c_7594,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k10_relat_1(sK4,X0_51)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k10_relat_1(sK4,sK0(sK2,sK3,sK4))
    | k10_relat_1(sK4,X0_51) != k10_relat_1(sK4,sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4665])).

cnf(c_7596,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k10_relat_1(sK4,sK0(sK2,sK3,sK4))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k10_relat_1(sK4,k1_xboole_0)
    | k10_relat_1(sK4,k1_xboole_0) != k10_relat_1(sK4,sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7594])).

cnf(c_6384,plain,
    ( X0_51 != X1_51
    | X0_51 = sK0(sK2,X0_52,sK4)
    | sK0(sK2,X0_52,sK4) != X1_51 ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_6385,plain,
    ( sK0(sK2,sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = sK0(sK2,sK3,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6384])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_struct_0(X2)) = k2_struct_0(X1)
    | k2_struct_0(X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,k2_struct_0(X2)) = k2_struct_0(X1)
    | k2_struct_0(X2) = k1_xboole_0
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_355,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X0)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(sK4)
    | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_struct_0(X1)) = k2_struct_0(X0)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_359,plain,
    ( ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_struct_0(X1)) = k2_struct_0(X0)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_24])).

cnf(c_360,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0)
    | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k2_struct_0(X1)) = k2_struct_0(X0)
    | k2_struct_0(X1) = k1_xboole_0
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_359])).

cnf(c_1777,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_struct_0(X1_52)
    | ~ l1_struct_0(X0_52)
    | k8_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,k2_struct_0(X1_52)) = k2_struct_0(X0_52)
    | k2_struct_0(X1_52) = k1_xboole_0
    | u1_struct_0(X1_52) != u1_struct_0(sK3)
    | u1_struct_0(X0_52) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_2305,plain,
    ( k8_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,k2_struct_0(X1_52)) = k2_struct_0(X0_52)
    | k2_struct_0(X1_52) = k1_xboole_0
    | u1_struct_0(X1_52) != u1_struct_0(sK3)
    | u1_struct_0(X0_52) != u1_struct_0(sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1777])).

cnf(c_3621,plain,
    ( k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,k2_struct_0(sK3)) = k2_struct_0(X0_52)
    | k2_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(X0_52) != u1_struct_0(sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2305])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1780,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2302,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1786,plain,
    ( l1_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2296,plain,
    ( l1_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1786])).

cnf(c_2731,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2302,c_2296])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1788,plain,
    ( ~ l1_struct_0(X0_52)
    | k2_struct_0(X0_52) = u1_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2294,plain,
    ( k2_struct_0(X0_52) = u1_struct_0(X0_52)
    | l1_struct_0(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_2827,plain,
    ( k2_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_2731,c_2294])).

cnf(c_3622,plain,
    ( k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,u1_struct_0(sK3)) = k2_struct_0(X0_52)
    | k2_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(X0_52) != u1_struct_0(sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3621,c_2827])).

cnf(c_3623,plain,
    ( k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,u1_struct_0(sK3)) = k2_struct_0(X0_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK2)
    | u1_struct_0(sK3) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(X0_52) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3622,c_2827])).

cnf(c_34,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1820,plain,
    ( l1_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1786])).

cnf(c_1822,plain,
    ( l1_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_4839,plain,
    ( l1_struct_0(X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | u1_struct_0(sK3) = k1_xboole_0
    | u1_struct_0(X0_52) != u1_struct_0(sK2)
    | k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,u1_struct_0(sK3)) = k2_struct_0(X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3623,c_34,c_1822])).

cnf(c_4840,plain,
    ( k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,u1_struct_0(sK3)) = k2_struct_0(X0_52)
    | u1_struct_0(X0_52) != u1_struct_0(sK2)
    | u1_struct_0(sK3) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4839])).

cnf(c_4848,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK3)) = k2_struct_0(sK2)
    | u1_struct_0(sK3) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4840])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1778,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2304,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1778])).

cnf(c_2732,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2304,c_2296])).

cnf(c_2873,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_2732,c_2294])).

cnf(c_4849,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK3)) = u1_struct_0(sK2)
    | u1_struct_0(sK3) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4848,c_2873])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1781,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2301,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1781])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1784,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k8_relset_1(X1_51,X2_51,X0_51,X3_51) = k10_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2298,plain,
    ( k8_relset_1(X0_51,X1_51,X2_51,X3_51) = k10_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1784])).

cnf(c_3168,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51) = k10_relat_1(sK4,X0_51) ),
    inference(superposition,[status(thm)],[c_2301,c_2298])).

cnf(c_4850,plain,
    ( k10_relat_1(sK4,u1_struct_0(sK3)) = u1_struct_0(sK2)
    | u1_struct_0(sK3) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4849,c_3168])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5126,plain,
    ( k10_relat_1(sK4,u1_struct_0(sK3)) = u1_struct_0(sK2)
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4850,c_37,c_2732])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_459,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_460,plain,
    ( v5_pre_topc(sK4,X0,X1)
    | m1_subset_1(sK0(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | m1_subset_1(sK0(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(X1)))
    | v5_pre_topc(sK4,X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_24])).

cnf(c_465,plain,
    ( v5_pre_topc(sK4,X0,X1)
    | m1_subset_1(sK0(X0,X1,sK4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_1774,plain,
    ( v5_pre_topc(sK4,X0_52,X1_52)
    | m1_subset_1(sK0(X0_52,X1_52,sK4),k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK3)
    | u1_struct_0(X0_52) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_2308,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(X1_52) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,X1_52,X0_52) = iProver_top
    | m1_subset_1(sK0(X1_52,X0_52,sK4),k1_zfmisc_1(u1_struct_0(X0_52))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_3740,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2308])).

cnf(c_1791,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_2565,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(c_2569,plain,
    ( v5_pre_topc(sK4,X0_52,sK3)
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3))))
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0_52) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_2573,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2569])).

cnf(c_4541,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3740,c_34])).

cnf(c_4542,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK0(X0_52,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4541])).

cnf(c_4550,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4542])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,negated_conjecture,
    ( ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( v5_pre_topc(sK4,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2650,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(c_2790,plain,
    ( v5_pre_topc(sK4,sK2,X0_52)
    | m1_subset_1(sK0(sK2,X0_52,sK4),k1_zfmisc_1(u1_struct_0(X0_52)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52))))
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_2792,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,sK2,X0_52) = iProver_top
    | m1_subset_1(sK0(sK2,X0_52,sK4),k1_zfmisc_1(u1_struct_0(X0_52))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2790])).

cnf(c_2794,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_5326,plain,
    ( m1_subset_1(sK0(sK2,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4550,c_31,c_34,c_37,c_38,c_2565,c_2650,c_2794])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_772,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) = X0
    | sK3 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_773,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_pre_topc(X0,sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) = X0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_26,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) = X0
    | sK3 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_717,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_pre_topc(X0,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) = X0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_721,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_pre_topc(X0,sK3)
    | u1_struct_0(sK3) = X0
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_717,c_27,c_25])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_pre_topc(X0,sK3)
    | u1_struct_0(sK3) = X0
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_27,c_25,c_717])).

cnf(c_1771,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_pre_topc(X0_51,sK3)
    | u1_struct_0(sK3) = X0_51
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_775])).

cnf(c_2311,plain,
    ( u1_struct_0(sK3) = X0_51
    | k1_xboole_0 = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v4_pre_topc(X0_51,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1771])).

cnf(c_5331,plain,
    ( sK0(sK2,sK3,sK4) = u1_struct_0(sK3)
    | sK0(sK2,sK3,sK4) = k1_xboole_0
    | v4_pre_topc(sK0(sK2,sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5326,c_2311])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_492,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v4_pre_topc(sK0(X1,X2,X0),X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_23])).

cnf(c_493,plain,
    ( v5_pre_topc(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v4_pre_topc(sK0(X0,X1,sK4),X1)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_497,plain,
    ( v4_pre_topc(sK0(X0,X1,sK4),X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v5_pre_topc(sK4,X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_24])).

cnf(c_498,plain,
    ( v5_pre_topc(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v4_pre_topc(sK0(X0,X1,sK4),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_1773,plain,
    ( v5_pre_topc(sK4,X0_52,X1_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v4_pre_topc(sK0(X0_52,X1_52,sK4),X1_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK3)
    | u1_struct_0(X0_52) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_498])).

cnf(c_2649,plain,
    ( v5_pre_topc(sK4,sK2,X0_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52))))
    | v4_pre_topc(sK0(sK2,X0_52,sK4),X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_2651,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,sK2,X0_52) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v4_pre_topc(sK0(sK2,X0_52,sK4),X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2649])).

cnf(c_2653,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v4_pre_topc(sK0(sK2,sK3,sK4),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_5407,plain,
    ( sK0(sK2,sK3,sK4) = k1_xboole_0
    | sK0(sK2,sK3,sK4) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5331,c_31,c_34,c_37,c_38,c_2565,c_2653,c_2650])).

cnf(c_5408,plain,
    ( sK0(sK2,sK3,sK4) = u1_struct_0(sK3)
    | sK0(sK2,sK3,sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5407])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_525,plain,
    ( v5_pre_topc(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X1,X2,X0)),X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_526,plain,
    ( v5_pre_topc(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4)),X0)
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4)),X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v5_pre_topc(sK4,X0,X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_24])).

cnf(c_531,plain,
    ( v5_pre_topc(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,sK0(X0,X1,sK4)),X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_530])).

cnf(c_1772,plain,
    ( v5_pre_topc(sK4,X0_52,X1_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(X1_52),sK4,sK0(X0_52,X1_52,sK4)),X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK3)
    | u1_struct_0(X0_52) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_531])).

cnf(c_2310,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(X1_52) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,X1_52,X0_52) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(X0_52)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1_52),u1_struct_0(X0_52),sK4,sK0(X1_52,X0_52,sK4)),X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1772])).

cnf(c_3088,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2310])).

cnf(c_2567,plain,
    ( v5_pre_topc(sK4,X0_52,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(X0_52) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_2577,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_4053,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3088,c_34,c_2565,c_2577])).

cnf(c_4054,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK2)
    | v5_pre_topc(sK4,X0_52,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK3)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X0_52),u1_struct_0(sK3),sK4,sK0(X0_52,sK3,sK4)),X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4053])).

cnf(c_4062,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4054])).

cnf(c_4063,plain,
    ( v5_pre_topc(sK4,sK2,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top
    | v4_pre_topc(k10_relat_1(sK4,sK0(sK2,sK3,sK4)),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4062,c_3168])).

cnf(c_4104,plain,
    ( v4_pre_topc(k10_relat_1(sK4,sK0(sK2,sK3,sK4)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4063,c_31,c_37,c_38])).

cnf(c_5413,plain,
    ( sK0(sK2,sK3,sK4) = k1_xboole_0
    | v4_pre_topc(k10_relat_1(sK4,u1_struct_0(sK3)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5408,c_4104])).

cnf(c_5427,plain,
    ( sK0(sK2,sK3,sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0
    | v4_pre_topc(u1_struct_0(sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5126,c_5413])).

cnf(c_10,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_922,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_923,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_922])).

cnf(c_925,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_923,c_28])).

cnf(c_1762,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(subtyping,[status(esa)],[c_925])).

cnf(c_2320,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_3276,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2873,c_2320])).

cnf(c_5578,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | sK0(sK2,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5427,c_3276])).

cnf(c_5579,plain,
    ( sK0(sK2,sK3,sK4) = k1_xboole_0
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5578])).

cnf(c_5586,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v4_pre_topc(k10_relat_1(sK4,k1_xboole_0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5579,c_4104])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1789,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2293,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_2685,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_2293])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1785,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2779,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_2780,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2779])).

cnf(c_2997,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2685,c_2780])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1783,plain,
    ( ~ v1_relat_1(X0_51)
    | k10_relat_1(X0_51,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2299,plain,
    ( k10_relat_1(X0_51,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_3002,plain,
    ( k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2997,c_2299])).

cnf(c_5589,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v4_pre_topc(k1_xboole_0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5586,c_3002])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_332,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v4_pre_topc(k1_xboole_0,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_852,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v4_pre_topc(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_29])).

cnf(c_853,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(k1_xboole_0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_854,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v4_pre_topc(k1_xboole_0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1787,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | m1_subset_1(k8_relset_1(X1_51,X2_51,X0_51,X3_51),k1_zfmisc_1(X1_51)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2295,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(k8_relset_1(X1_51,X2_51,X0_51,X3_51),k1_zfmisc_1(X1_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1787])).

cnf(c_3312,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_51),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_2295])).

cnf(c_3856,plain,
    ( m1_subset_1(k10_relat_1(sK4,X0_51),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3312,c_37])).

cnf(c_3863,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3002,c_3856])).

cnf(c_5795,plain,
    ( u1_struct_0(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5589,c_31,c_854,c_3863])).

cnf(c_5800,plain,
    ( sK0(sK2,sK3,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5795,c_5408])).

cnf(c_1794,plain,
    ( ~ v4_pre_topc(X0_51,X0_52)
    | v4_pre_topc(X1_51,X0_52)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_3036,plain,
    ( ~ v4_pre_topc(X0_51,sK2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)),sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != X0_51 ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_4607,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51),sK2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)),sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_3036])).

cnf(c_4610,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)),sK2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0),sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4607])).

cnf(c_3197,plain,
    ( X0_51 != X1_51
    | X0_51 = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X2_51)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X2_51) != X1_51 ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_3799,plain,
    ( X0_51 = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51)
    | X0_51 != k10_relat_1(sK4,X1_51)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51) != k10_relat_1(sK4,X1_51) ),
    inference(instantiation,[status(thm)],[c_3197])).

cnf(c_4606,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51) != k10_relat_1(sK4,X0_51)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k10_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_3799])).

cnf(c_4608,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) != k10_relat_1(sK4,k1_xboole_0)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) != k10_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4606])).

cnf(c_2595,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51) = k10_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_4404,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)) = k10_relat_1(sK4,sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2595])).

cnf(c_4264,plain,
    ( X0_51 != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51) = X0_51
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51) ),
    inference(instantiation,[status(thm)],[c_3794])).

cnf(c_4266,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4264])).

cnf(c_3955,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_51) != k10_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_3799])).

cnf(c_3956,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) != k10_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3955])).

cnf(c_3951,plain,
    ( X0_51 != X1_51
    | X0_51 = k10_relat_1(sK4,X2_51)
    | k10_relat_1(sK4,X2_51) != X1_51 ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_3952,plain,
    ( k10_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k10_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3951])).

cnf(c_3880,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3863])).

cnf(c_3800,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) != k10_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0)
    | k1_xboole_0 != k10_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3799])).

cnf(c_3265,plain,
    ( ~ v4_pre_topc(X0_51,sK2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51),sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X1_51) != X0_51 ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_3267,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0),sK2)
    | ~ v4_pre_topc(k1_xboole_0,sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3265])).

cnf(c_2939,plain,
    ( ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_2788,plain,
    ( v5_pre_topc(sK4,sK2,X0_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X0_52),sK4,sK0(sK2,X0_52,sK4)),sK2)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0_52) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_2801,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK0(sK2,sK3,sK4)),sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2788])).

cnf(c_2686,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2685])).

cnf(c_2597,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k1_xboole_0) = k10_relat_1(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2595])).

cnf(c_1813,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7597,c_7596,c_6385,c_5800,c_4610,c_4608,c_4404,c_4266,c_3956,c_3952,c_3880,c_3800,c_3267,c_2939,c_2801,c_2779,c_2686,c_2650,c_2597,c_2565,c_1813,c_853,c_21,c_22,c_25,c_28])).


%------------------------------------------------------------------------------
