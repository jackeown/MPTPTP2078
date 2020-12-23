%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1901+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:50 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 637 expanded)
%              Number of clauses        :   90 ( 197 expanded)
%              Number of leaves         :   23 ( 148 expanded)
%              Depth                    :   20
%              Number of atoms          :  677 (2156 expanded)
%              Number of equality atoms :  172 ( 454 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f81,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | m1_subset_1(sK1(X0),k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f81,f78])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( ( l1_pre_topc(X1)
                & v2_pre_topc(X1)
                & ~ v2_struct_0(X1) )
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                 => v5_pre_topc(X2,X0,X1) ) )
         => v1_tdlat_3(X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f42,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f43,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,
    ( ? [X0] :
        ( ~ v1_tdlat_3(X0)
        & ! [X1] :
            ( ! [X2] :
                ( v5_pre_topc(X2,X0,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
            | ~ l1_pre_topc(X1)
            | ~ v2_pre_topc(X1)
            | v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v1_tdlat_3(sK2)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,sK2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ v1_tdlat_3(sK2)
    & ! [X1] :
        ( ! [X2] :
            ( v5_pre_topc(X2,sK2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            | ~ v1_funct_1(X2) )
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f52])).

fof(f84,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ~ v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f79,f76,f78])).

fof(f7,axiom,(
    ! [X0] : l1_pre_topc(k1_compts_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : l1_pre_topc(k1_compts_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) = k1_compts_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) = k1_compts_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f96,plain,(
    ! [X0] : l1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f65,f62])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) ) ),
    inference(definition_unfolding,[],[f63,f78,f78])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) ) ),
    inference(definition_unfolding,[],[f74,f78,f78])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X2,X1] :
      ( v5_pre_topc(X2,sK2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    ! [X2,X1] :
      ( v5_pre_topc(X2,sK2,X1)
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_unfolding,[],[f86,f78])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f72,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] : v1_tdlat_3(k1_compts_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : v1_tdlat_3(k1_compts_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,(
    ! [X0] : v1_tdlat_3(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f73,f62])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X0,X1,X2)),X0)
        & v4_pre_topc(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f58,f78,f78])).

fof(f80,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f80,f78])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f68,f76,f78])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f67,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k1_compts_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k1_compts_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k1_compts_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f70,f62])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v4_pre_topc(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,plain,
    ( m1_subset_1(sK1(X0),k9_setfam_1(u1_struct_0(X0)))
    | v1_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_927,plain,
    ( m1_subset_1(sK1(X0),k9_setfam_1(u1_struct_0(X0)))
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_928,plain,
    ( m1_subset_1(sK1(sK2),k9_setfam_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_927])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26,negated_conjecture,
    ( ~ v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_40,plain,
    ( m1_subset_1(sK1(sK2),k9_setfam_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_930,plain,
    ( m1_subset_1(sK1(sK2),k9_setfam_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_928,c_29,c_28,c_26,c_40])).

cnf(c_2558,plain,
    ( m1_subset_1(sK1(sK2),k9_setfam_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | k8_relset_1(X1,X1,k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2568,plain,
    ( k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3365,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK2),k6_relat_1(u1_struct_0(sK2)),sK1(sK2)) = sK1(sK2) ),
    inference(superposition,[status(thm)],[c_2558,c_2568])).

cnf(c_10,plain,
    ( l1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2575,plain,
    ( l1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2578,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3691,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))),u1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))))) = g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))
    | v1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2575,c_2578])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2785,plain,
    ( ~ m1_subset_1(k2_subset_1(k9_setfam_1(X0)),k9_setfam_1(k9_setfam_1(X0)))
    | v1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( m1_subset_1(k2_subset_1(X0),k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2786,plain,
    ( m1_subset_1(k2_subset_1(k9_setfam_1(X0)),k9_setfam_1(k9_setfam_1(X0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2950,plain,
    ( ~ l1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))))
    | ~ v1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))),u1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))))) = g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4598,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))),u1_pre_topc(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))))) = g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3691,c_10,c_2785,c_2786,c_2950])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2570,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k9_setfam_1(k9_setfam_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4602,plain,
    ( g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) != g1_pre_topc(X1,X2)
    | u1_struct_0(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) = X1
    | m1_subset_1(X2,k9_setfam_1(k9_setfam_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4598,c_2570])).

cnf(c_4765,plain,
    ( u1_struct_0(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) = X0
    | m1_subset_1(k2_subset_1(k9_setfam_1(X0)),k9_setfam_1(k9_setfam_1(X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4602])).

cnf(c_2791,plain,
    ( m1_subset_1(k2_subset_1(k9_setfam_1(X0)),k9_setfam_1(k9_setfam_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2786])).

cnf(c_4783,plain,
    ( u1_struct_0(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4765,c_2791])).

cnf(c_3,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,negated_conjecture,
    ( v5_pre_topc(X0,sK2,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_17,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_425,plain,
    ( v5_pre_topc(X0,sK2,X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_17])).

cnf(c_426,plain,
    ( v5_pre_topc(k6_relat_1(X0),sK2,X1)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_889,plain,
    ( v5_pre_topc(k6_relat_1(X0),sK2,X1)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_426])).

cnf(c_890,plain,
    ( v5_pre_topc(k6_relat_1(X0),sK2,X1)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_2556,plain,
    ( v5_pre_topc(k6_relat_1(X0),sK2,X1) = iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_4807,plain,
    ( v5_pre_topc(k6_relat_1(X0),sK2,g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),u1_struct_0(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1))))) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) != iProver_top
    | v2_struct_0(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | v1_tdlat_3(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_2556])).

cnf(c_4814,plain,
    ( v5_pre_topc(k6_relat_1(X0),sK2,g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),X1) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) != iProver_top
    | v2_struct_0(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | v1_tdlat_3(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4807,c_4783])).

cnf(c_18,plain,
    ( v1_tdlat_3(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2572,plain,
    ( v1_tdlat_3(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5032,plain,
    ( v5_pre_topc(k6_relat_1(X0),sK2,g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),X1) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) != iProver_top
    | v2_struct_0(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4814,c_2575,c_2572])).

cnf(c_7,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_449,plain,
    ( ~ v5_pre_topc(X0,X1,X2)
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3),X1)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k6_relat_1(X4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_450,plain,
    ( ~ v5_pre_topc(k6_relat_1(X0),X1,X2)
    | ~ v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),u1_struct_0(X2))
    | ~ v4_pre_topc(X3,X2)
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k6_relat_1(X0),X3),X1)
    | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X2)))
    | ~ m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_2562,plain,
    ( v5_pre_topc(k6_relat_1(X0),X1,X2) != iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v4_pre_topc(X3,X2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),k6_relat_1(X0),X3),X1) = iProver_top
    | m1_subset_1(X3,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_5826,plain,
    ( v5_pre_topc(k6_relat_1(X0),X1,g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2)))) != iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),u1_struct_0(g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2))))) != iProver_top
    | v4_pre_topc(X3,g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),X2,k6_relat_1(X0),X3),X1) = iProver_top
    | m1_subset_1(X3,k9_setfam_1(u1_struct_0(g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2)))))) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2))))))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_2562])).

cnf(c_5836,plain,
    ( v5_pre_topc(k6_relat_1(X0),X1,g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2)))) != iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),X2) != iProver_top
    | v4_pre_topc(X3,g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2)))) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),X2,k6_relat_1(X0),X3),X1) = iProver_top
    | m1_subset_1(X3,k9_setfam_1(X2)) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X1),X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5826,c_4783])).

cnf(c_25,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_911,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X2)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_912,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_2555,plain,
    ( v4_pre_topc(X0,X1) = iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1))) != iProver_top
    | v1_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_4806,plain,
    ( v4_pre_topc(X0,g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
    | v1_tdlat_3(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4783,c_2555])).

cnf(c_5681,plain,
    ( v4_pre_topc(X0,g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4806,c_2575,c_2572])).

cnf(c_7417,plain,
    ( v5_pre_topc(k6_relat_1(X0),X1,g1_pre_topc(X2,k2_subset_1(k9_setfam_1(X2)))) != iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(X1),X2) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),X2,k6_relat_1(X0),X3),X1) = iProver_top
    | m1_subset_1(X3,k9_setfam_1(X2)) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X1),X2))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5836,c_2575,c_5681])).

cnf(c_7421,plain,
    ( v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),X1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),X1,k6_relat_1(X0),X2),sK2) = iProver_top
    | m1_subset_1(X2,k9_setfam_1(X1)) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) != iProver_top
    | v2_struct_0(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5032,c_7417])).

cnf(c_33,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7568,plain,
    ( v2_struct_0(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) != iProver_top
    | m1_subset_1(X2,k9_setfam_1(X1)) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),X1,k6_relat_1(X0),X2),sK2) = iProver_top
    | v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7421,c_33])).

cnf(c_7569,plain,
    ( v1_funct_2(k6_relat_1(X0),u1_struct_0(sK2),X1) != iProver_top
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),X1,k6_relat_1(X0),X2),sK2) = iProver_top
    | m1_subset_1(X2,k9_setfam_1(X1)) != iProver_top
    | m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),X1))) != iProver_top
    | v2_struct_0(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7568])).

cnf(c_7581,plain,
    ( v1_funct_2(k6_relat_1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v4_pre_topc(sK1(sK2),sK2) = iProver_top
    | m1_subset_1(sK1(sK2),k9_setfam_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK2),k2_subset_1(k9_setfam_1(u1_struct_0(sK2))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3365,c_7569])).

cnf(c_12,plain,
    ( m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2981,plain,
    ( m1_subset_1(k6_relat_1(u1_struct_0(X0)),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2982,plain,
    ( m1_subset_1(k6_relat_1(u1_struct_0(X0)),k9_setfam_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2981])).

cnf(c_2984,plain,
    ( m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2982])).

cnf(c_1,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_13,plain,
    ( v1_partfun1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_367,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X1
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_368,plain,
    ( v1_funct_2(k6_relat_1(X0),X0,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_372,plain,
    ( ~ m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(k6_relat_1(X0),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_17])).

cnf(c_373,plain,
    ( v1_funct_2(k6_relat_1(X0),X0,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X1))) ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_2804,plain,
    ( v1_funct_2(k6_relat_1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_2806,plain,
    ( v1_funct_2(k6_relat_1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(k6_relat_1(u1_struct_0(sK2)),k9_setfam_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2804])).

cnf(c_15,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0)))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_14,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_388,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_14,c_16])).

cnf(c_406,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(g1_pre_topc(X1,k2_subset_1(k9_setfam_1(X1))))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_388])).

cnf(c_407,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),k2_subset_1(k9_setfam_1(u1_struct_0(X0)))))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_408,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(g1_pre_topc(u1_struct_0(X0),k2_subset_1(k9_setfam_1(u1_struct_0(X0))))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_410,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK2),k2_subset_1(k9_setfam_1(u1_struct_0(sK2))))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_23,plain,
    ( ~ v4_pre_topc(sK1(X0),X0)
    | v1_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,plain,
    ( v4_pre_topc(sK1(X0),X0) != iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_44,plain,
    ( v4_pre_topc(sK1(sK2),sK2) != iProver_top
    | v1_tdlat_3(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_39,plain,
    ( m1_subset_1(sK1(X0),k9_setfam_1(u1_struct_0(X0))) = iProver_top
    | v1_tdlat_3(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_41,plain,
    ( m1_subset_1(sK1(sK2),k9_setfam_1(u1_struct_0(sK2))) = iProver_top
    | v1_tdlat_3(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_37,plain,
    ( v1_tdlat_3(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7581,c_2984,c_2806,c_410,c_44,c_41,c_37,c_33,c_32,c_31])).


%------------------------------------------------------------------------------
