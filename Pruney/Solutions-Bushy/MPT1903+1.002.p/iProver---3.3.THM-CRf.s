%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1903+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:51 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 539 expanded)
%              Number of clauses        :   91 ( 173 expanded)
%              Number of leaves         :   20 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          :  656 (2596 expanded)
%              Number of equality atoms :  185 ( 518 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
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

fof(f32,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f70,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X1,X0) ) )
       => v2_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( ( l1_pre_topc(X1)
                & v2_pre_topc(X1)
                & ~ v2_struct_0(X1) )
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X2) )
                 => v5_pre_topc(X2,X1,X0) ) )
         => v2_tdlat_3(X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f44,plain,
    ( ? [X0] :
        ( ~ v2_tdlat_3(X0)
        & ! [X1] :
            ( ! [X2] :
                ( v5_pre_topc(X2,X1,X0)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(X2) )
            | ~ l1_pre_topc(X1)
            | ~ v2_pre_topc(X1)
            | v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v2_tdlat_3(sK2)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X1,sK2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ v2_tdlat_3(sK2)
    & ! [X1] :
        ( ! [X2] :
            ( v5_pre_topc(X2,X1,sK2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
            | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
            | ~ v1_funct_1(X2) )
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f44])).

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ~ v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f6,axiom,(
    ! [X0] : l1_pre_topc(k2_tex_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : l1_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : g1_pre_topc(X0,k1_tex_1(X0)) = k2_tex_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : g1_pre_topc(X0,k1_tex_1(X0)) = k2_tex_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f79,plain,(
    ! [X0] : l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_tdlat_3(k2_tex_1(X0))
      & v2_pre_topc(k2_tex_1(X0))
      & v1_pre_topc(k2_tex_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v1_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0] : v1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f60,f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_tex_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_tex_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f5])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | v4_pre_topc(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_tex_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tex_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tex_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f53])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f61,plain,(
    ! [X0] : v2_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X0] : v2_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f77,plain,(
    ! [X2,X1] :
      ( v5_pre_topc(X2,X1,sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ! [X2,X0] :
      ( u1_struct_0(X0) = X2
      | k1_xboole_0 = X2
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ! [X0] : v2_tdlat_3(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X0] : v2_tdlat_3(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f62,f53])).

fof(f73,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | u1_struct_0(X0) != sK1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X0] :
      ( v2_tdlat_3(X0)
      | k1_xboole_0 != sK1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_24,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_812,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_813,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_812])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_26,negated_conjecture,
    ( ~ v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_815,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_813,c_29,c_28,c_26,c_40])).

cnf(c_2242,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_relset_1(X1,X1,k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2253,plain,
    ( k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2858,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k6_relat_1(u1_struct_0(sK2)),sK1(sK2)) = sK1(sK2) ),
    inference(superposition,[status(thm)],[c_2242,c_2253])).

cnf(c_8,plain,
    ( l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2258,plain,
    ( l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2260,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3172,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))),u1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))) = g1_pre_topc(X0,k1_tex_1(X0))
    | v1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2258,c_2260])).

cnf(c_15,plain,
    ( v1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_345,plain,
    ( ~ l1_pre_topc(X0)
    | g1_pre_topc(X1,k1_tex_1(X1)) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_346,plain,
    ( ~ l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))),u1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))) = g1_pre_topc(X0,k1_tex_1(X0)) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_3386,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))),u1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))) = g1_pre_topc(X0,k1_tex_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3172,c_8,c_346])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2254,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3389,plain,
    ( g1_pre_topc(X0,k1_tex_1(X0)) != g1_pre_topc(X1,X2)
    | u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X1
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3386,c_2254])).

cnf(c_3525,plain,
    ( u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X0
    | m1_subset_1(k1_tex_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3389])).

cnf(c_7,plain,
    ( m1_subset_1(k1_tex_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_88,plain,
    ( m1_subset_1(k1_tex_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3543,plain,
    ( u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3525,c_88])).

cnf(c_6,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_439,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k6_relat_1(X4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_440,plain,
    ( ~ v5_pre_topc(k6_relat_1(X0),X1,X2)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),u1_struct_0(X2))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k6_relat_1(X0),X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_2248,plain,
    ( v5_pre_topc(k6_relat_1(X0),X1,X2) != iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k6_relat_1(X0),X3),X1) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_4998,plain,
    ( v5_pre_topc(k6_relat_1(X0),g1_pre_topc(X1,k1_tex_1(X1)),X2) != iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))),u1_struct_0(X2)) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(X1,u1_struct_0(X2),k6_relat_1(X0),X3),g1_pre_topc(X1,k1_tex_1(X1))) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3543,c_2248])).

cnf(c_5065,plain,
    ( v5_pre_topc(k6_relat_1(X0),g1_pre_topc(X1,k1_tex_1(X1)),X2) != iProver_top
    | v1_funct_2(k6_relat_1(X0),X1,u1_struct_0(X2)) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(X1,u1_struct_0(X2),k6_relat_1(X0),X3),g1_pre_topc(X1,k1_tex_1(X1))) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4998,c_3543])).

cnf(c_5490,plain,
    ( v5_pre_topc(k6_relat_1(X0),g1_pre_topc(X1,k1_tex_1(X1)),X2) != iProver_top
    | v1_funct_2(k6_relat_1(X0),X1,u1_struct_0(X2)) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(X1,u1_struct_0(X2),k6_relat_1(X0),X3),g1_pre_topc(X1,k1_tex_1(X1))) = iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5065,c_2258])).

cnf(c_5494,plain,
    ( v5_pre_topc(k6_relat_1(u1_struct_0(sK2)),g1_pre_topc(u1_struct_0(sK2),k1_tex_1(u1_struct_0(sK2))),sK2) != iProver_top
    | v1_funct_2(k6_relat_1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v4_pre_topc(sK1(sK2),g1_pre_topc(u1_struct_0(sK2),k1_tex_1(u1_struct_0(sK2)))) = iProver_top
    | v4_pre_topc(sK1(sK2),sK2) != iProver_top
    | m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2858,c_5490])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_32,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_33,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_37,plain,
    ( v2_tdlat_3(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_39,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_41,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_tdlat_3(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_23,plain,
    ( v4_pre_topc(sK1(X0),X0)
    | ~ v2_pre_topc(X0)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,plain,
    ( v4_pre_topc(sK1(X0),X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_44,plain,
    ( v4_pre_topc(sK1(sK2),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_tdlat_3(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_11,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_378,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_11,c_12])).

cnf(c_17,plain,
    ( ~ v2_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_396,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(g1_pre_topc(X1,k1_tex_1(X1)))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_378,c_17])).

cnf(c_397,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),k1_tex_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_398,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(g1_pre_topc(u1_struct_0(X0),k1_tex_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_400,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK2),k1_tex_1(u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_1,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10,plain,
    ( v1_partfun1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_357,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X1
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_358,plain,
    ( v1_funct_2(k6_relat_1(X0),X0,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_362,plain,
    ( ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(k6_relat_1(X0),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_16])).

cnf(c_363,plain,
    ( v1_funct_2(k6_relat_1(X0),X0,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_2451,plain,
    ( v1_funct_2(k6_relat_1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_2453,plain,
    ( v1_funct_2(k6_relat_1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2451])).

cnf(c_9,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2727,plain,
    ( m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2728,plain,
    ( m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2727])).

cnf(c_2257,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14,plain,
    ( v2_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27,negated_conjecture,
    ( v5_pre_topc(X0,X1,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_415,plain,
    ( v5_pre_topc(X0,X1,sK2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_16])).

cnf(c_416,plain,
    ( v5_pre_topc(k6_relat_1(X0),X1,sK2)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),u1_struct_0(sK2))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_764,plain,
    ( v5_pre_topc(k6_relat_1(X0),X1,sK2)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),u1_struct_0(sK2))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(X2,k1_tex_1(X2)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_416])).

cnf(c_765,plain,
    ( v5_pre_topc(k6_relat_1(X0),g1_pre_topc(X1,k1_tex_1(X1)),sK2)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))),u1_struct_0(sK2))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))),u1_struct_0(sK2))))
    | v2_struct_0(g1_pre_topc(X1,k1_tex_1(X1)))
    | ~ l1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_779,plain,
    ( v5_pre_topc(k6_relat_1(X0),g1_pre_topc(X1,k1_tex_1(X1)),sK2)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))),u1_struct_0(sK2))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))),u1_struct_0(sK2))))
    | v2_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_765,c_8])).

cnf(c_2244,plain,
    ( v5_pre_topc(k6_relat_1(X0),g1_pre_topc(X1,k1_tex_1(X1)),sK2) = iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_3547,plain,
    ( v5_pre_topc(k6_relat_1(X0),g1_pre_topc(X1,k1_tex_1(X1)),sK2) = iProver_top
    | v1_funct_2(k6_relat_1(X0),X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3543,c_2244])).

cnf(c_3676,plain,
    ( v5_pre_topc(k6_relat_1(u1_struct_0(sK2)),g1_pre_topc(u1_struct_0(sK2),k1_tex_1(u1_struct_0(sK2))),sK2) = iProver_top
    | v1_funct_2(k6_relat_1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK2),k1_tex_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2257,c_3547])).

cnf(c_5571,plain,
    ( v4_pre_topc(sK1(sK2),g1_pre_topc(u1_struct_0(sK2),k1_tex_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5494,c_31,c_32,c_33,c_37,c_41,c_44,c_400,c_2453,c_2728,c_3676])).

cnf(c_25,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_787,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(X2,k1_tex_1(X2)) != X1
    | u1_struct_0(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_788,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(X1,k1_tex_1(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1)))))
    | ~ v2_tdlat_3(g1_pre_topc(X1,k1_tex_1(X1)))
    | ~ l1_pre_topc(g1_pre_topc(X1,k1_tex_1(X1)))
    | u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = X0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_13,plain,
    ( v2_tdlat_3(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_804,plain,
    ( ~ v4_pre_topc(X0,g1_pre_topc(X1,k1_tex_1(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1)))))
    | u1_struct_0(g1_pre_topc(X1,k1_tex_1(X1))) = X0
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_788,c_8,c_13])).

cnf(c_2243,plain,
    ( u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X1
    | k1_xboole_0 = X1
    | v4_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_3550,plain,
    ( X0 = X1
    | k1_xboole_0 = X0
    | v4_pre_topc(X0,g1_pre_topc(X1,k1_tex_1(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3543,c_2243])).

cnf(c_5576,plain,
    ( sK1(sK2) = u1_struct_0(sK2)
    | sK1(sK2) = k1_xboole_0
    | m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5571,c_3550])).

cnf(c_21,plain,
    ( ~ v2_pre_topc(X0)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK1(X0) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_49,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_22,plain,
    ( ~ v2_pre_topc(X0)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_46,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5576,c_49,c_46,c_41,c_37,c_26,c_33,c_28,c_32,c_29])).


%------------------------------------------------------------------------------
