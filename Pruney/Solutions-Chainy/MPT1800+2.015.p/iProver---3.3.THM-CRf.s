%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:05 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  176 (4089 expanded)
%              Number of clauses        :  114 ( 822 expanded)
%              Number of leaves         :   12 ( 964 expanded)
%              Depth                    :   26
%              Number of atoms          :  736 (34011 expanded)
%              Number of equality atoms :  199 (6099 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK2)
          | ~ m1_pre_topc(sK2,X0)
          | ~ v1_tsep_1(sK2,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK2)
          | ( m1_pre_topc(sK2,X0)
            & v1_tsep_1(sK2,X0) ) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,X1)
            | ~ m1_pre_topc(X1,sK1)
            | ~ v1_tsep_1(X1,sK1) )
          & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,X1)
            | ( m1_pre_topc(X1,sK1)
              & v1_tsep_1(X1,sK1) ) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
      | ~ m1_pre_topc(sK2,sK1)
      | ~ v1_tsep_1(sK2,sK1) )
    & ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
      | ( m1_pre_topc(sK2,sK1)
        & v1_tsep_1(sK2,sK1) ) )
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f60,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f61,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,negated_conjecture,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v1_tsep_1(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_213,plain,
    ( ~ v1_tsep_1(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(prop_impl,[status(thm)],[c_21,c_18])).

cnf(c_595,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_213])).

cnf(c_596,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v3_pre_topc(sK0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_598,plain,
    ( ~ v3_pre_topc(sK0(sK1,sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_23,c_21])).

cnf(c_1976,plain,
    ( ~ v3_pre_topc(sK0(sK1,sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_598])).

cnf(c_2832,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | v3_pre_topc(sK0(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1976])).

cnf(c_17,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_147,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_21])).

cnf(c_699,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_147])).

cnf(c_700,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_702,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_23])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_940,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X0,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_940,c_24,c_23])).

cnf(c_1748,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_702,c_944])).

cnf(c_1749,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1748])).

cnf(c_1928,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1749])).

cnf(c_2870,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,u1_struct_0(sK2))
    | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1928])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_1018,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_1017])).

cnf(c_1022,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1018,c_24,c_23])).

cnf(c_1163,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK1,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1022])).

cnf(c_1164,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_1163])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1053,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_1054,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k6_tmap_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1053])).

cnf(c_1168,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1164,c_24,c_23,c_1054])).

cnf(c_1709,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_702,c_1168])).

cnf(c_1710,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))),u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2)))) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1709])).

cnf(c_1934,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))),u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2)))) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1710])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_981,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_982,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_981])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_982,c_24,c_23])).

cnf(c_1733,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1)
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_702,c_986])).

cnf(c_1734,plain,
    ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1733])).

cnf(c_1930,plain,
    ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1734])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_999,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_999])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1000,c_24,c_23])).

cnf(c_1728,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0)
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_702,c_1004])).

cnf(c_1729,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1728])).

cnf(c_1931,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1729])).

cnf(c_15,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_159,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_17])).

cnf(c_160,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_159])).

cnf(c_691,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0))
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_160,c_147])).

cnf(c_692,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_694,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_25,c_24,c_23,c_22])).

cnf(c_1972,plain,
    ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_694])).

cnf(c_2889,plain,
    ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1931,c_1972])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_718,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_147])).

cnf(c_719,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_721,plain,
    ( v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_25,c_24,c_23])).

cnf(c_1131,plain,
    ( ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_721])).

cnf(c_1132,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1131])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_740,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_147])).

cnf(c_741,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | l1_pre_topc(k8_tmap_1(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_793,plain,
    ( ~ l1_pre_topc(X0)
    | k8_tmap_1(sK1,sK2) != X0
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_721])).

cnf(c_794,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_793])).

cnf(c_1134,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1132,c_25,c_24,c_23,c_741,c_794])).

cnf(c_1968,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_1134])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_710,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_147])).

cnf(c_711,plain,
    ( v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_710])).

cnf(c_713,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_711,c_25,c_24,c_23,c_22])).

cnf(c_1971,plain,
    ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_713])).

cnf(c_2896,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1968,c_1971])).

cnf(c_2919,plain,
    ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1934,c_1930,c_2889,c_2896])).

cnf(c_2935,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2870,c_2919])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_960,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_961,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(X0,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_960])).

cnf(c_965,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(X0,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_961,c_24,c_23])).

cnf(c_1738,plain,
    ( v3_pre_topc(X0,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_702,c_965])).

cnf(c_1739,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_1738])).

cnf(c_1929,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1739])).

cnf(c_2869,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,u1_struct_0(sK2))
    | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_2930,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2869,c_2919])).

cnf(c_4,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_176,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_17])).

cnf(c_20,negated_conjecture,
    ( v1_tsep_1(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_215,plain,
    ( v1_tsep_1(sK2,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_609,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_215])).

cnf(c_610,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v3_pre_topc(u1_struct_0(sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_612,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_23,c_21])).

cnf(c_1975,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_612])).

cnf(c_2833,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_2933,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2930,c_2833])).

cnf(c_2938,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2935,c_2933])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_584,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_213])).

cnf(c_585,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_587,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_23,c_21])).

cnf(c_1977,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_587])).

cnf(c_2939,plain,
    ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,sK2)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(demodulation,[status(thm)],[c_2938,c_1977])).

cnf(c_2941,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_2939])).

cnf(c_2944,plain,
    ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,sK2)
    | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2832,c_2938,c_2941])).

cnf(c_2945,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2944])).

cnf(c_2947,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2945,c_2933])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.13/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/0.99  
% 2.13/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/0.99  
% 2.13/0.99  ------  iProver source info
% 2.13/0.99  
% 2.13/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.13/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/0.99  git: non_committed_changes: false
% 2.13/0.99  git: last_make_outside_of_git: false
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/0.99  --bmc1_property_lemmas                  false
% 2.13/0.99  --bmc1_k_induction                      false
% 2.13/0.99  --bmc1_non_equiv_states                 false
% 2.13/0.99  --bmc1_deadlock                         false
% 2.13/0.99  --bmc1_ucm                              false
% 2.13/0.99  --bmc1_add_unsat_core                   none
% 2.13/0.99  --bmc1_unsat_core_children              false
% 2.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/0.99  --bmc1_out_stat                         full
% 2.13/0.99  --bmc1_ground_init                      false
% 2.13/0.99  --bmc1_pre_inst_next_state              false
% 2.13/0.99  --bmc1_pre_inst_state                   false
% 2.13/0.99  --bmc1_pre_inst_reach_state             false
% 2.13/0.99  --bmc1_out_unsat_core                   false
% 2.13/0.99  --bmc1_aig_witness_out                  false
% 2.13/0.99  --bmc1_verbose                          false
% 2.13/0.99  --bmc1_dump_clauses_tptp                false
% 2.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.13/0.99  --bmc1_dump_file                        -
% 2.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.13/0.99  --bmc1_ucm_extend_mode                  1
% 2.13/0.99  --bmc1_ucm_init_mode                    2
% 2.13/0.99  --bmc1_ucm_cone_mode                    none
% 2.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.13/0.99  --bmc1_ucm_relax_model                  4
% 2.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/0.99  --bmc1_ucm_layered_model                none
% 2.13/0.99  --bmc1_ucm_max_lemma_size               10
% 2.13/0.99  
% 2.13/0.99  ------ AIG Options
% 2.13/0.99  
% 2.13/0.99  --aig_mode                              false
% 2.13/0.99  
% 2.13/0.99  ------ Instantiation Options
% 2.13/0.99  
% 2.13/0.99  --instantiation_flag                    true
% 2.13/0.99  --inst_sos_flag                         false
% 2.13/0.99  --inst_sos_phase                        true
% 2.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/0.99  --inst_lit_sel_side                     num_symb
% 2.13/0.99  --inst_solver_per_active                1400
% 2.13/0.99  --inst_solver_calls_frac                1.
% 2.13/0.99  --inst_passive_queue_type               priority_queues
% 2.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/0.99  --inst_passive_queues_freq              [25;2]
% 2.13/0.99  --inst_dismatching                      true
% 2.13/0.99  --inst_eager_unprocessed_to_passive     true
% 2.13/0.99  --inst_prop_sim_given                   true
% 2.13/0.99  --inst_prop_sim_new                     false
% 2.13/0.99  --inst_subs_new                         false
% 2.13/0.99  --inst_eq_res_simp                      false
% 2.13/0.99  --inst_subs_given                       false
% 2.13/0.99  --inst_orphan_elimination               true
% 2.13/0.99  --inst_learning_loop_flag               true
% 2.13/0.99  --inst_learning_start                   3000
% 2.13/0.99  --inst_learning_factor                  2
% 2.13/0.99  --inst_start_prop_sim_after_learn       3
% 2.13/0.99  --inst_sel_renew                        solver
% 2.13/0.99  --inst_lit_activity_flag                true
% 2.13/0.99  --inst_restr_to_given                   false
% 2.13/0.99  --inst_activity_threshold               500
% 2.13/0.99  --inst_out_proof                        true
% 2.13/0.99  
% 2.13/0.99  ------ Resolution Options
% 2.13/0.99  
% 2.13/0.99  --resolution_flag                       true
% 2.13/0.99  --res_lit_sel                           adaptive
% 2.13/0.99  --res_lit_sel_side                      none
% 2.13/0.99  --res_ordering                          kbo
% 2.13/0.99  --res_to_prop_solver                    active
% 2.13/0.99  --res_prop_simpl_new                    false
% 2.13/0.99  --res_prop_simpl_given                  true
% 2.13/0.99  --res_passive_queue_type                priority_queues
% 2.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/0.99  --res_passive_queues_freq               [15;5]
% 2.13/0.99  --res_forward_subs                      full
% 2.13/0.99  --res_backward_subs                     full
% 2.13/0.99  --res_forward_subs_resolution           true
% 2.13/0.99  --res_backward_subs_resolution          true
% 2.13/0.99  --res_orphan_elimination                true
% 2.13/0.99  --res_time_limit                        2.
% 2.13/0.99  --res_out_proof                         true
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Options
% 2.13/0.99  
% 2.13/0.99  --superposition_flag                    true
% 2.13/0.99  --sup_passive_queue_type                priority_queues
% 2.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.13/0.99  --demod_completeness_check              fast
% 2.13/0.99  --demod_use_ground                      true
% 2.13/0.99  --sup_to_prop_solver                    passive
% 2.13/0.99  --sup_prop_simpl_new                    true
% 2.13/0.99  --sup_prop_simpl_given                  true
% 2.13/0.99  --sup_fun_splitting                     false
% 2.13/0.99  --sup_smt_interval                      50000
% 2.13/0.99  
% 2.13/0.99  ------ Superposition Simplification Setup
% 2.13/0.99  
% 2.13/0.99  --sup_indices_passive                   []
% 2.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_full_bw                           [BwDemod]
% 2.13/0.99  --sup_immed_triv                        [TrivRules]
% 2.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_immed_bw_main                     []
% 2.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/0.99  
% 2.13/0.99  ------ Combination Options
% 2.13/0.99  
% 2.13/0.99  --comb_res_mult                         3
% 2.13/0.99  --comb_sup_mult                         2
% 2.13/0.99  --comb_inst_mult                        10
% 2.13/0.99  
% 2.13/0.99  ------ Debug Options
% 2.13/0.99  
% 2.13/0.99  --dbg_backtrace                         false
% 2.13/0.99  --dbg_dump_prop_clauses                 false
% 2.13/0.99  --dbg_dump_prop_clauses_file            -
% 2.13/0.99  --dbg_out_stat                          false
% 2.13/0.99  ------ Parsing...
% 2.13/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/0.99  ------ Proving...
% 2.13/0.99  ------ Problem Properties 
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  clauses                                 52
% 2.13/0.99  conjectures                             2
% 2.13/0.99  EPR                                     2
% 2.13/0.99  Horn                                    38
% 2.13/0.99  unary                                   12
% 2.13/0.99  binary                                  19
% 2.13/0.99  lits                                    154
% 2.13/0.99  lits eq                                 70
% 2.13/0.99  fd_pure                                 0
% 2.13/0.99  fd_pseudo                               0
% 2.13/0.99  fd_cond                                 0
% 2.13/0.99  fd_pseudo_cond                          0
% 2.13/0.99  AC symbols                              0
% 2.13/0.99  
% 2.13/0.99  ------ Schedule dynamic 5 is on 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/0.99  
% 2.13/0.99  
% 2.13/0.99  ------ 
% 2.13/0.99  Current options:
% 2.13/0.99  ------ 
% 2.13/0.99  
% 2.13/0.99  ------ Input Options
% 2.13/0.99  
% 2.13/0.99  --out_options                           all
% 2.13/0.99  --tptp_safe_out                         true
% 2.13/0.99  --problem_path                          ""
% 2.13/0.99  --include_path                          ""
% 2.13/0.99  --clausifier                            res/vclausify_rel
% 2.13/0.99  --clausifier_options                    --mode clausify
% 2.13/0.99  --stdin                                 false
% 2.13/0.99  --stats_out                             all
% 2.13/0.99  
% 2.13/0.99  ------ General Options
% 2.13/0.99  
% 2.13/0.99  --fof                                   false
% 2.13/0.99  --time_out_real                         305.
% 2.13/0.99  --time_out_virtual                      -1.
% 2.13/0.99  --symbol_type_check                     false
% 2.13/0.99  --clausify_out                          false
% 2.13/0.99  --sig_cnt_out                           false
% 2.13/0.99  --trig_cnt_out                          false
% 2.13/0.99  --trig_cnt_out_tolerance                1.
% 2.13/0.99  --trig_cnt_out_sk_spl                   false
% 2.13/0.99  --abstr_cl_out                          false
% 2.13/0.99  
% 2.13/0.99  ------ Global Options
% 2.13/0.99  
% 2.13/0.99  --schedule                              default
% 2.13/0.99  --add_important_lit                     false
% 2.13/0.99  --prop_solver_per_cl                    1000
% 2.13/0.99  --min_unsat_core                        false
% 2.13/0.99  --soft_assumptions                      false
% 2.13/0.99  --soft_lemma_size                       3
% 2.13/0.99  --prop_impl_unit_size                   0
% 2.13/0.99  --prop_impl_unit                        []
% 2.13/0.99  --share_sel_clauses                     true
% 2.13/0.99  --reset_solvers                         false
% 2.13/0.99  --bc_imp_inh                            [conj_cone]
% 2.13/0.99  --conj_cone_tolerance                   3.
% 2.13/0.99  --extra_neg_conj                        none
% 2.13/0.99  --large_theory_mode                     true
% 2.13/0.99  --prolific_symb_bound                   200
% 2.13/0.99  --lt_threshold                          2000
% 2.13/0.99  --clause_weak_htbl                      true
% 2.13/0.99  --gc_record_bc_elim                     false
% 2.13/0.99  
% 2.13/0.99  ------ Preprocessing Options
% 2.13/0.99  
% 2.13/0.99  --preprocessing_flag                    true
% 2.13/0.99  --time_out_prep_mult                    0.1
% 2.13/0.99  --splitting_mode                        input
% 2.13/0.99  --splitting_grd                         true
% 2.13/0.99  --splitting_cvd                         false
% 2.13/0.99  --splitting_cvd_svl                     false
% 2.13/0.99  --splitting_nvd                         32
% 2.13/0.99  --sub_typing                            true
% 2.13/0.99  --prep_gs_sim                           true
% 2.13/0.99  --prep_unflatten                        true
% 2.13/0.99  --prep_res_sim                          true
% 2.13/0.99  --prep_upred                            true
% 2.13/0.99  --prep_sem_filter                       exhaustive
% 2.13/0.99  --prep_sem_filter_out                   false
% 2.13/0.99  --pred_elim                             true
% 2.13/0.99  --res_sim_input                         true
% 2.13/0.99  --eq_ax_congr_red                       true
% 2.13/0.99  --pure_diseq_elim                       true
% 2.13/0.99  --brand_transform                       false
% 2.13/0.99  --non_eq_to_eq                          false
% 2.13/0.99  --prep_def_merge                        true
% 2.13/0.99  --prep_def_merge_prop_impl              false
% 2.13/0.99  --prep_def_merge_mbd                    true
% 2.13/0.99  --prep_def_merge_tr_red                 false
% 2.13/0.99  --prep_def_merge_tr_cl                  false
% 2.13/0.99  --smt_preprocessing                     true
% 2.13/0.99  --smt_ac_axioms                         fast
% 2.13/0.99  --preprocessed_out                      false
% 2.13/0.99  --preprocessed_stats                    false
% 2.13/0.99  
% 2.13/0.99  ------ Abstraction refinement Options
% 2.13/0.99  
% 2.13/0.99  --abstr_ref                             []
% 2.13/0.99  --abstr_ref_prep                        false
% 2.13/0.99  --abstr_ref_until_sat                   false
% 2.13/0.99  --abstr_ref_sig_restrict                funpre
% 2.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/0.99  --abstr_ref_under                       []
% 2.13/0.99  
% 2.13/0.99  ------ SAT Options
% 2.13/0.99  
% 2.13/0.99  --sat_mode                              false
% 2.13/0.99  --sat_fm_restart_options                ""
% 2.13/0.99  --sat_gr_def                            false
% 2.13/0.99  --sat_epr_types                         true
% 2.13/0.99  --sat_non_cyclic_types                  false
% 2.13/0.99  --sat_finite_models                     false
% 2.13/0.99  --sat_fm_lemmas                         false
% 2.13/0.99  --sat_fm_prep                           false
% 2.13/0.99  --sat_fm_uc_incr                        true
% 2.13/0.99  --sat_out_model                         small
% 2.13/0.99  --sat_out_clauses                       false
% 2.13/0.99  
% 2.13/0.99  ------ QBF Options
% 2.13/0.99  
% 2.13/0.99  --qbf_mode                              false
% 2.13/0.99  --qbf_elim_univ                         false
% 2.13/0.99  --qbf_dom_inst                          none
% 2.13/0.99  --qbf_dom_pre_inst                      false
% 2.13/0.99  --qbf_sk_in                             false
% 2.13/0.99  --qbf_pred_elim                         true
% 2.13/0.99  --qbf_split                             512
% 2.13/0.99  
% 2.13/0.99  ------ BMC1 Options
% 2.13/0.99  
% 2.13/0.99  --bmc1_incremental                      false
% 2.13/0.99  --bmc1_axioms                           reachable_all
% 2.13/0.99  --bmc1_min_bound                        0
% 2.13/0.99  --bmc1_max_bound                        -1
% 2.13/0.99  --bmc1_max_bound_default                -1
% 2.13/0.99  --bmc1_symbol_reachability              true
% 2.13/1.00  --bmc1_property_lemmas                  false
% 2.13/1.00  --bmc1_k_induction                      false
% 2.13/1.00  --bmc1_non_equiv_states                 false
% 2.13/1.00  --bmc1_deadlock                         false
% 2.13/1.00  --bmc1_ucm                              false
% 2.13/1.00  --bmc1_add_unsat_core                   none
% 2.13/1.00  --bmc1_unsat_core_children              false
% 2.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/1.00  --bmc1_out_stat                         full
% 2.13/1.00  --bmc1_ground_init                      false
% 2.13/1.00  --bmc1_pre_inst_next_state              false
% 2.13/1.00  --bmc1_pre_inst_state                   false
% 2.13/1.00  --bmc1_pre_inst_reach_state             false
% 2.13/1.00  --bmc1_out_unsat_core                   false
% 2.13/1.00  --bmc1_aig_witness_out                  false
% 2.13/1.00  --bmc1_verbose                          false
% 2.13/1.00  --bmc1_dump_clauses_tptp                false
% 2.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.13/1.00  --bmc1_dump_file                        -
% 2.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.13/1.00  --bmc1_ucm_extend_mode                  1
% 2.13/1.00  --bmc1_ucm_init_mode                    2
% 2.13/1.00  --bmc1_ucm_cone_mode                    none
% 2.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.13/1.00  --bmc1_ucm_relax_model                  4
% 2.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/1.00  --bmc1_ucm_layered_model                none
% 2.13/1.00  --bmc1_ucm_max_lemma_size               10
% 2.13/1.00  
% 2.13/1.00  ------ AIG Options
% 2.13/1.00  
% 2.13/1.00  --aig_mode                              false
% 2.13/1.00  
% 2.13/1.00  ------ Instantiation Options
% 2.13/1.00  
% 2.13/1.00  --instantiation_flag                    true
% 2.13/1.00  --inst_sos_flag                         false
% 2.13/1.00  --inst_sos_phase                        true
% 2.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel_side                     none
% 2.13/1.00  --inst_solver_per_active                1400
% 2.13/1.00  --inst_solver_calls_frac                1.
% 2.13/1.00  --inst_passive_queue_type               priority_queues
% 2.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/1.00  --inst_passive_queues_freq              [25;2]
% 2.13/1.00  --inst_dismatching                      true
% 2.13/1.00  --inst_eager_unprocessed_to_passive     true
% 2.13/1.00  --inst_prop_sim_given                   true
% 2.13/1.00  --inst_prop_sim_new                     false
% 2.13/1.00  --inst_subs_new                         false
% 2.13/1.00  --inst_eq_res_simp                      false
% 2.13/1.00  --inst_subs_given                       false
% 2.13/1.00  --inst_orphan_elimination               true
% 2.13/1.00  --inst_learning_loop_flag               true
% 2.13/1.00  --inst_learning_start                   3000
% 2.13/1.00  --inst_learning_factor                  2
% 2.13/1.00  --inst_start_prop_sim_after_learn       3
% 2.13/1.00  --inst_sel_renew                        solver
% 2.13/1.00  --inst_lit_activity_flag                true
% 2.13/1.00  --inst_restr_to_given                   false
% 2.13/1.00  --inst_activity_threshold               500
% 2.13/1.00  --inst_out_proof                        true
% 2.13/1.00  
% 2.13/1.00  ------ Resolution Options
% 2.13/1.00  
% 2.13/1.00  --resolution_flag                       false
% 2.13/1.00  --res_lit_sel                           adaptive
% 2.13/1.00  --res_lit_sel_side                      none
% 2.13/1.00  --res_ordering                          kbo
% 2.13/1.00  --res_to_prop_solver                    active
% 2.13/1.00  --res_prop_simpl_new                    false
% 2.13/1.00  --res_prop_simpl_given                  true
% 2.13/1.00  --res_passive_queue_type                priority_queues
% 2.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/1.00  --res_passive_queues_freq               [15;5]
% 2.13/1.00  --res_forward_subs                      full
% 2.13/1.00  --res_backward_subs                     full
% 2.13/1.00  --res_forward_subs_resolution           true
% 2.13/1.00  --res_backward_subs_resolution          true
% 2.13/1.00  --res_orphan_elimination                true
% 2.13/1.00  --res_time_limit                        2.
% 2.13/1.00  --res_out_proof                         true
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Options
% 2.13/1.00  
% 2.13/1.00  --superposition_flag                    true
% 2.13/1.00  --sup_passive_queue_type                priority_queues
% 2.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.13/1.00  --demod_completeness_check              fast
% 2.13/1.00  --demod_use_ground                      true
% 2.13/1.00  --sup_to_prop_solver                    passive
% 2.13/1.00  --sup_prop_simpl_new                    true
% 2.13/1.00  --sup_prop_simpl_given                  true
% 2.13/1.00  --sup_fun_splitting                     false
% 2.13/1.00  --sup_smt_interval                      50000
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Simplification Setup
% 2.13/1.00  
% 2.13/1.00  --sup_indices_passive                   []
% 2.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_full_bw                           [BwDemod]
% 2.13/1.00  --sup_immed_triv                        [TrivRules]
% 2.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_immed_bw_main                     []
% 2.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  
% 2.13/1.00  ------ Combination Options
% 2.13/1.00  
% 2.13/1.00  --comb_res_mult                         3
% 2.13/1.00  --comb_sup_mult                         2
% 2.13/1.00  --comb_inst_mult                        10
% 2.13/1.00  
% 2.13/1.00  ------ Debug Options
% 2.13/1.00  
% 2.13/1.00  --dbg_backtrace                         false
% 2.13/1.00  --dbg_dump_prop_clauses                 false
% 2.13/1.00  --dbg_dump_prop_clauses_file            -
% 2.13/1.00  --dbg_out_stat                          false
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  ------ Proving...
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  % SZS status Theorem for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00   Resolution empty clause
% 2.13/1.00  
% 2.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  fof(f2,axiom,(
% 2.13/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f13,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f2])).
% 2.13/1.00  
% 2.13/1.00  fof(f14,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f13])).
% 2.13/1.00  
% 2.13/1.00  fof(f28,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f14])).
% 2.13/1.00  
% 2.13/1.00  fof(f29,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(rectify,[],[f28])).
% 2.13/1.00  
% 2.13/1.00  fof(f30,plain,(
% 2.13/1.00    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f31,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.13/1.00  
% 2.13/1.00  fof(f42,plain,(
% 2.13/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK0(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f9,conjecture,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f10,negated_conjecture,(
% 2.13/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 2.13/1.00    inference(negated_conjecture,[],[f9])).
% 2.13/1.00  
% 2.13/1.00  fof(f26,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f10])).
% 2.13/1.00  
% 2.13/1.00  fof(f27,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f26])).
% 2.13/1.00  
% 2.13/1.00  fof(f33,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f27])).
% 2.13/1.00  
% 2.13/1.00  fof(f34,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f33])).
% 2.13/1.00  
% 2.13/1.00  fof(f36,plain,(
% 2.13/1.00    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK2) | ~m1_pre_topc(sK2,X0) | ~v1_tsep_1(sK2,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK2) | (m1_pre_topc(sK2,X0) & v1_tsep_1(sK2,X0))) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f35,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,X1) | ~m1_pre_topc(X1,sK1) | ~v1_tsep_1(X1,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,X1) | (m1_pre_topc(X1,sK1) & v1_tsep_1(X1,sK1))) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f37,plain,(
% 2.13/1.00    ((g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)) & (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | (m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1))) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 2.13/1.00  
% 2.13/1.00  fof(f60,plain,(
% 2.13/1.00    m1_pre_topc(sK2,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f63,plain,(
% 2.13/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) | ~m1_pre_topc(sK2,sK1) | ~v1_tsep_1(sK2,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f58,plain,(
% 2.13/1.00    l1_pre_topc(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f8,axiom,(
% 2.13/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f25,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f8])).
% 2.13/1.00  
% 2.13/1.00  fof(f55,plain,(
% 2.13/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f25])).
% 2.13/1.00  
% 2.13/1.00  fof(f62,plain,(
% 2.13/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | m1_pre_topc(sK2,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f6,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f21,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f6])).
% 2.13/1.00  
% 2.13/1.00  fof(f22,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f21])).
% 2.13/1.00  
% 2.13/1.00  fof(f32,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f22])).
% 2.13/1.00  
% 2.13/1.00  fof(f51,plain,(
% 2.13/1.00    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f32])).
% 2.13/1.00  
% 2.13/1.00  fof(f56,plain,(
% 2.13/1.00    ~v2_struct_0(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f57,plain,(
% 2.13/1.00    v2_pre_topc(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f1,axiom,(
% 2.13/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f11,plain,(
% 2.13/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f1])).
% 2.13/1.00  
% 2.13/1.00  fof(f12,plain,(
% 2.13/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(flattening,[],[f11])).
% 2.13/1.00  
% 2.13/1.00  fof(f38,plain,(
% 2.13/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f12])).
% 2.13/1.00  
% 2.13/1.00  fof(f3,axiom,(
% 2.13/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f15,plain,(
% 2.13/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f3])).
% 2.13/1.00  
% 2.13/1.00  fof(f16,plain,(
% 2.13/1.00    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f15])).
% 2.13/1.00  
% 2.13/1.00  fof(f43,plain,(
% 2.13/1.00    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f16])).
% 2.13/1.00  
% 2.13/1.00  fof(f45,plain,(
% 2.13/1.00    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f16])).
% 2.13/1.00  
% 2.13/1.00  fof(f5,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f19,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f5])).
% 2.13/1.00  
% 2.13/1.00  fof(f20,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f19])).
% 2.13/1.00  
% 2.13/1.00  fof(f49,plain,(
% 2.13/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f20])).
% 2.13/1.00  
% 2.13/1.00  fof(f50,plain,(
% 2.13/1.00    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f20])).
% 2.13/1.00  
% 2.13/1.00  fof(f7,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f23,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f7])).
% 2.13/1.00  
% 2.13/1.00  fof(f24,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f23])).
% 2.13/1.00  
% 2.13/1.00  fof(f54,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f24])).
% 2.13/1.00  
% 2.13/1.00  fof(f65,plain,(
% 2.13/1.00    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(equality_resolution,[],[f54])).
% 2.13/1.00  
% 2.13/1.00  fof(f59,plain,(
% 2.13/1.00    ~v2_struct_0(sK2)),
% 2.13/1.00    inference(cnf_transformation,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f4,axiom,(
% 2.13/1.00    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f17,plain,(
% 2.13/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f4])).
% 2.13/1.00  
% 2.13/1.00  fof(f18,plain,(
% 2.13/1.00    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f17])).
% 2.13/1.00  
% 2.13/1.00  fof(f46,plain,(
% 2.13/1.00    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f18])).
% 2.13/1.00  
% 2.13/1.00  fof(f48,plain,(
% 2.13/1.00    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f18])).
% 2.13/1.00  
% 2.13/1.00  fof(f53,plain,(
% 2.13/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f24])).
% 2.13/1.00  
% 2.13/1.00  fof(f52,plain,(
% 2.13/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f32])).
% 2.13/1.00  
% 2.13/1.00  fof(f39,plain,(
% 2.13/1.00    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f64,plain,(
% 2.13/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(equality_resolution,[],[f39])).
% 2.13/1.00  
% 2.13/1.00  fof(f61,plain,(
% 2.13/1.00    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) | v1_tsep_1(sK2,sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f41,plain,(
% 2.13/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | ~ v3_pre_topc(sK0(X1,X0),X1)
% 2.13/1.00      | v1_tsep_1(X0,X1)
% 2.13/1.00      | ~ l1_pre_topc(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_21,negated_conjecture,
% 2.13/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_18,negated_conjecture,
% 2.13/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.13/1.00      | ~ v1_tsep_1(sK2,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_213,plain,
% 2.13/1.00      ( ~ v1_tsep_1(sK2,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(prop_impl,[status(thm)],[c_21,c_18]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_595,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | ~ v3_pre_topc(sK0(X1,X0),X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.13/1.00      | sK2 != X0
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_213]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_596,plain,
% 2.13/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.13/1.00      | ~ v3_pre_topc(sK0(sK1,sK2),sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_595]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_23,negated_conjecture,
% 2.13/1.00      ( l1_pre_topc(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_598,plain,
% 2.13/1.00      ( ~ v3_pre_topc(sK0(sK1,sK2),sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_596,c_23,c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1976,plain,
% 2.13/1.00      ( ~ v3_pre_topc(sK0(sK1,sK2),sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_598]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2832,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.13/1.00      | v3_pre_topc(sK0(sK1,sK2),sK1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1976]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_17,plain,
% 2.13/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | ~ l1_pre_topc(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_19,negated_conjecture,
% 2.13/1.00      ( m1_pre_topc(sK2,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_147,negated_conjecture,
% 2.13/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.13/1.00      inference(global_propositional_subsumption,[status(thm)],[c_19,c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_699,plain,
% 2.13/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | sK2 != X0
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_147]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_700,plain,
% 2.13/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ l1_pre_topc(sK1) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_699]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_702,plain,
% 2.13/1.00      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.13/1.00      inference(global_propositional_subsumption,[status(thm)],[c_700,c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_14,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ v3_pre_topc(X0,X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_25,negated_conjecture,
% 2.13/1.00      ( ~ v2_struct_0(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_939,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ v3_pre_topc(X0,X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_940,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ v3_pre_topc(X0,sK1)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_939]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_24,negated_conjecture,
% 2.13/1.00      ( v2_pre_topc(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_944,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ v3_pre_topc(X0,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_940,c_24,c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1748,plain,
% 2.13/1.00      ( ~ v3_pre_topc(X0,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,X0)
% 2.13/1.00      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.13/1.00      | u1_struct_0(sK2) != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_702,c_944]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1749,plain,
% 2.13/1.00      ( ~ v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1748]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1928,plain,
% 2.13/1.00      ( ~ v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_1749]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2870,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k6_tmap_1(sK1,u1_struct_0(sK2))
% 2.13/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1928]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_0,plain,
% 2.13/1.00      ( ~ l1_pre_topc(X0)
% 2.13/1.00      | ~ v1_pre_topc(X0)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.13/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_7,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | v1_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1017,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | v1_pre_topc(k6_tmap_1(X1,X0))
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1018,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1017]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1022,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | v1_pre_topc(k6_tmap_1(sK1,X0)) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_1018,c_24,c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1163,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | k6_tmap_1(sK1,X0) != X1
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_1022]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1164,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ l1_pre_topc(k6_tmap_1(sK1,X0))
% 2.13/1.00      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1163]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_5,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | l1_pre_topc(k6_tmap_1(X1,X0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1053,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | l1_pre_topc(k6_tmap_1(X1,X0))
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1054,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | l1_pre_topc(k6_tmap_1(sK1,X0))
% 2.13/1.00      | ~ l1_pre_topc(sK1) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1053]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1168,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_1164,c_24,c_23,c_1054]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1709,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,X0)),u1_pre_topc(k6_tmap_1(sK1,X0))) = k6_tmap_1(sK1,X0)
% 2.13/1.00      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.13/1.00      | u1_struct_0(sK2) != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_702,c_1168]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1710,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))),u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2)))) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1709]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1934,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))),u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2)))) = k6_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_1710]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_12,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_981,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | u1_struct_0(k6_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_982,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_981]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_986,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_982,c_24,c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1733,plain,
% 2.13/1.00      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.13/1.00      | u1_struct_0(k6_tmap_1(sK1,X0)) = u1_struct_0(sK1)
% 2.13/1.00      | u1_struct_0(sK2) != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_702,c_986]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1734,plain,
% 2.13/1.00      ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1733]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1930,plain,
% 2.13/1.00      ( u1_struct_0(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_struct_0(sK1) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_1734]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_11,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_999,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1000,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_999]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1004,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_1000,c_24,c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1728,plain,
% 2.13/1.00      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.13/1.00      | u1_pre_topc(k6_tmap_1(sK1,X0)) = k5_tmap_1(sK1,X0)
% 2.13/1.00      | u1_struct_0(sK2) != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_702,c_1004]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1729,plain,
% 2.13/1.00      ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1728]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1931,plain,
% 2.13/1.00      ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = k5_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_1729]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_15,plain,
% 2.13/1.00      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_159,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.13/1.00      inference(global_propositional_subsumption,[status(thm)],[c_15,c_17]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_160,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_159]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_691,plain,
% 2.13/1.00      ( v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0))
% 2.13/1.00      | sK2 != X0
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_160,c_147]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_692,plain,
% 2.13/1.00      ( v2_struct_0(sK2)
% 2.13/1.00      | v2_struct_0(sK1)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_691]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_22,negated_conjecture,
% 2.13/1.00      ( ~ v2_struct_0(sK2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_694,plain,
% 2.13/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_692,c_25,c_24,c_23,c_22]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1972,plain,
% 2.13/1.00      ( k5_tmap_1(sK1,u1_struct_0(sK2)) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_694]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2889,plain,
% 2.13/1.00      ( u1_pre_topc(k6_tmap_1(sK1,u1_struct_0(sK2))) = u1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1931,c_1972]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_10,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | v1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_718,plain,
% 2.13/1.00      ( v2_struct_0(X0)
% 2.13/1.00      | ~ v2_pre_topc(X0)
% 2.13/1.00      | ~ l1_pre_topc(X0)
% 2.13/1.00      | v1_pre_topc(k8_tmap_1(X0,X1))
% 2.13/1.00      | sK2 != X1
% 2.13/1.00      | sK1 != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_147]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_719,plain,
% 2.13/1.00      ( v2_struct_0(sK1)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_718]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_721,plain,
% 2.13/1.00      ( v1_pre_topc(k8_tmap_1(sK1,sK2)) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_719,c_25,c_24,c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1131,plain,
% 2.13/1.00      ( ~ l1_pre_topc(X0)
% 2.13/1.00      | k8_tmap_1(sK1,sK2) != X0
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_721]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1132,plain,
% 2.13/1.00      ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.13/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1131]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_8,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_740,plain,
% 2.13/1.00      ( v2_struct_0(X0)
% 2.13/1.00      | ~ v2_pre_topc(X0)
% 2.13/1.00      | ~ l1_pre_topc(X0)
% 2.13/1.00      | l1_pre_topc(k8_tmap_1(X0,X1))
% 2.13/1.00      | sK2 != X1
% 2.13/1.00      | sK1 != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_147]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_741,plain,
% 2.13/1.00      ( v2_struct_0(sK1)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.13/1.00      | ~ l1_pre_topc(sK1) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_740]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_793,plain,
% 2.13/1.00      ( ~ l1_pre_topc(X0)
% 2.13/1.00      | k8_tmap_1(sK1,sK2) != X0
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_721]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_794,plain,
% 2.13/1.00      ( ~ l1_pre_topc(k8_tmap_1(sK1,sK2))
% 2.13/1.00      | g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_793]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1134,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_1132,c_25,c_24,c_23,c_741,c_794]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1968,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK1,sK2)),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_1134]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_16,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_710,plain,
% 2.13/1.00      ( v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1)
% 2.13/1.00      | sK2 != X0
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_147]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_711,plain,
% 2.13/1.00      ( v2_struct_0(sK2)
% 2.13/1.00      | v2_struct_0(sK1)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_710]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_713,plain,
% 2.13/1.00      ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_711,c_25,c_24,c_23,c_22]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1971,plain,
% 2.13/1.00      ( u1_struct_0(k8_tmap_1(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_713]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2896,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(k8_tmap_1(sK1,sK2))) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_1968,c_1971]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2919,plain,
% 2.13/1.00      ( k6_tmap_1(sK1,u1_struct_0(sK2)) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(light_normalisation,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_1934,c_1930,c_2889,c_2896]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2935,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
% 2.13/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_2870,c_2919]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_13,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | v3_pre_topc(X0,X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_960,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | v3_pre_topc(X0,X1)
% 2.13/1.00      | ~ v2_pre_topc(X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0)
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_961,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | v3_pre_topc(X0,sK1)
% 2.13/1.00      | ~ v2_pre_topc(sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,X0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_960]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_965,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.13/1.00      | v3_pre_topc(X0,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,X0) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_961,c_24,c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1738,plain,
% 2.13/1.00      ( v3_pre_topc(X0,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,X0)
% 2.13/1.00      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 2.13/1.00      | u1_struct_0(sK2) != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_702,c_965]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1739,plain,
% 2.13/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1738]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1929,plain,
% 2.13/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,u1_struct_0(sK2)) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_1739]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2869,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k6_tmap_1(sK1,u1_struct_0(sK2))
% 2.13/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2930,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.13/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_2869,c_2919]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4,plain,
% 2.13/1.00      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.13/1.00      | ~ v1_tsep_1(X0,X1)
% 2.13/1.00      | ~ l1_pre_topc(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_176,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.13/1.00      | ~ v1_tsep_1(X0,X1)
% 2.13/1.00      | ~ l1_pre_topc(X1) ),
% 2.13/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4,c_17]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_20,negated_conjecture,
% 2.13/1.00      ( v1_tsep_1(sK2,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_215,plain,
% 2.13/1.00      ( v1_tsep_1(sK2,sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_609,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
% 2.13/1.00      | sK2 != X0
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_176,c_215]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_610,plain,
% 2.13/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.13/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_609]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_612,plain,
% 2.13/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_610,c_23,c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1975,plain,
% 2.13/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_612]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2833,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2)
% 2.13/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1975]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2933,plain,
% 2.13/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1) = iProver_top ),
% 2.13/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2930,c_2833]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2938,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2935,c_2933]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | v1_tsep_1(X0,X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | sK0(X1,X0) = u1_struct_0(X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_584,plain,
% 2.13/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.13/1.00      | ~ l1_pre_topc(X1)
% 2.13/1.00      | sK0(X1,X0) = u1_struct_0(X0)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.13/1.00      | sK2 != X0
% 2.13/1.00      | sK1 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_213]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_585,plain,
% 2.13/1.00      ( ~ m1_pre_topc(sK2,sK1)
% 2.13/1.00      | ~ l1_pre_topc(sK1)
% 2.13/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_584]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_587,plain,
% 2.13/1.00      ( sK0(sK1,sK2) = u1_struct_0(sK2)
% 2.13/1.00      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_585,c_23,c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1977,plain,
% 2.13/1.00      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k8_tmap_1(sK1,sK2)
% 2.13/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.13/1.00      inference(subtyping,[status(esa)],[c_587]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2939,plain,
% 2.13/1.00      ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,sK2)
% 2.13/1.00      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.13/1.00      inference(demodulation,[status(thm)],[c_2938,c_1977]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2941,plain,
% 2.13/1.00      ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 2.13/1.00      inference(equality_resolution_simp,[status(thm)],[c_2939]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2944,plain,
% 2.13/1.00      ( k8_tmap_1(sK1,sK2) != k8_tmap_1(sK1,sK2)
% 2.13/1.00      | v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_2832,c_2938,c_2941]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2945,plain,
% 2.13/1.00      ( v3_pre_topc(u1_struct_0(sK2),sK1) != iProver_top ),
% 2.13/1.00      inference(equality_resolution_simp,[status(thm)],[c_2944]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2947,plain,
% 2.13/1.00      ( $false ),
% 2.13/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2945,c_2933]) ).
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  ------                               Statistics
% 2.13/1.00  
% 2.13/1.00  ------ General
% 2.13/1.00  
% 2.13/1.00  abstr_ref_over_cycles:                  0
% 2.13/1.00  abstr_ref_under_cycles:                 0
% 2.13/1.00  gc_basic_clause_elim:                   0
% 2.13/1.00  forced_gc_time:                         0
% 2.13/1.00  parsing_time:                           0.012
% 2.13/1.00  unif_index_cands_time:                  0.
% 2.13/1.00  unif_index_add_time:                    0.
% 2.13/1.00  orderings_time:                         0.
% 2.13/1.00  out_proof_time:                         0.018
% 2.13/1.00  total_time:                             0.113
% 2.13/1.00  num_of_symbols:                         53
% 2.13/1.00  num_of_terms:                           1231
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing
% 2.13/1.00  
% 2.13/1.00  num_of_splits:                          0
% 2.13/1.00  num_of_split_atoms:                     0
% 2.13/1.00  num_of_reused_defs:                     0
% 2.13/1.00  num_eq_ax_congr_red:                    6
% 2.13/1.00  num_of_sem_filtered_clauses:            1
% 2.13/1.00  num_of_subtypes:                        4
% 2.13/1.00  monotx_restored_types:                  0
% 2.13/1.00  sat_num_of_epr_types:                   0
% 2.13/1.00  sat_num_of_non_cyclic_types:            0
% 2.13/1.00  sat_guarded_non_collapsed_types:        0
% 2.13/1.00  num_pure_diseq_elim:                    0
% 2.13/1.00  simp_replaced_by:                       0
% 2.13/1.00  res_preprocessed:                       168
% 2.13/1.00  prep_upred:                             0
% 2.13/1.00  prep_unflattend:                        96
% 2.13/1.00  smt_new_axioms:                         0
% 2.13/1.00  pred_elim_cands:                        8
% 2.13/1.00  pred_elim:                              5
% 2.13/1.00  pred_elim_cl:                           -27
% 2.13/1.00  pred_elim_cycles:                       9
% 2.13/1.00  merged_defs:                            6
% 2.13/1.00  merged_defs_ncl:                        0
% 2.13/1.00  bin_hyper_res:                          6
% 2.13/1.00  prep_cycles:                            3
% 2.13/1.00  pred_elim_time:                         0.031
% 2.13/1.00  splitting_time:                         0.
% 2.13/1.00  sem_filter_time:                        0.
% 2.13/1.00  monotx_time:                            0.
% 2.13/1.00  subtype_inf_time:                       0.001
% 2.13/1.00  
% 2.13/1.00  ------ Problem properties
% 2.13/1.00  
% 2.13/1.00  clauses:                                52
% 2.13/1.00  conjectures:                            2
% 2.13/1.00  epr:                                    2
% 2.13/1.00  horn:                                   38
% 2.13/1.00  ground:                                 52
% 2.13/1.00  unary:                                  12
% 2.13/1.00  binary:                                 19
% 2.13/1.00  lits:                                   154
% 2.13/1.00  lits_eq:                                70
% 2.13/1.00  fd_pure:                                0
% 2.13/1.00  fd_pseudo:                              0
% 2.13/1.00  fd_cond:                                0
% 2.13/1.00  fd_pseudo_cond:                         0
% 2.13/1.00  ac_symbols:                             0
% 2.13/1.00  
% 2.13/1.00  ------ Propositional Solver
% 2.13/1.00  
% 2.13/1.00  prop_solver_calls:                      17
% 2.13/1.00  prop_fast_solver_calls:                 1399
% 2.13/1.00  smt_solver_calls:                       0
% 2.13/1.00  smt_fast_solver_calls:                  0
% 2.13/1.00  prop_num_of_clauses:                    482
% 2.13/1.00  prop_preprocess_simplified:             2993
% 2.13/1.00  prop_fo_subsumed:                       58
% 2.13/1.00  prop_solver_time:                       0.
% 2.13/1.00  smt_solver_time:                        0.
% 2.13/1.00  smt_fast_solver_time:                   0.
% 2.13/1.00  prop_fast_solver_time:                  0.
% 2.13/1.00  prop_unsat_core_time:                   0.
% 2.13/1.00  
% 2.13/1.00  ------ QBF
% 2.13/1.00  
% 2.13/1.00  qbf_q_res:                              0
% 2.13/1.00  qbf_num_tautologies:                    0
% 2.13/1.00  qbf_prep_cycles:                        0
% 2.13/1.00  
% 2.13/1.00  ------ BMC1
% 2.13/1.00  
% 2.13/1.00  bmc1_current_bound:                     -1
% 2.13/1.00  bmc1_last_solved_bound:                 -1
% 2.13/1.00  bmc1_unsat_core_size:                   -1
% 2.13/1.00  bmc1_unsat_core_parents_size:           -1
% 2.13/1.00  bmc1_merge_next_fun:                    0
% 2.13/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.13/1.00  
% 2.13/1.00  ------ Instantiation
% 2.13/1.00  
% 2.13/1.00  inst_num_of_clauses:                    71
% 2.13/1.00  inst_num_in_passive:                    0
% 2.13/1.00  inst_num_in_active:                     0
% 2.13/1.00  inst_num_in_unprocessed:                71
% 2.13/1.00  inst_num_of_loops:                      0
% 2.13/1.00  inst_num_of_learning_restarts:          0
% 2.13/1.00  inst_num_moves_active_passive:          0
% 2.13/1.00  inst_lit_activity:                      0
% 2.13/1.00  inst_lit_activity_moves:                0
% 2.13/1.00  inst_num_tautologies:                   0
% 2.13/1.00  inst_num_prop_implied:                  0
% 2.13/1.00  inst_num_existing_simplified:           0
% 2.13/1.00  inst_num_eq_res_simplified:             0
% 2.13/1.00  inst_num_child_elim:                    0
% 2.13/1.00  inst_num_of_dismatching_blockings:      0
% 2.13/1.00  inst_num_of_non_proper_insts:           0
% 2.13/1.00  inst_num_of_duplicates:                 0
% 2.13/1.00  inst_inst_num_from_inst_to_res:         0
% 2.13/1.00  inst_dismatching_checking_time:         0.
% 2.13/1.00  
% 2.13/1.00  ------ Resolution
% 2.13/1.00  
% 2.13/1.00  res_num_of_clauses:                     0
% 2.13/1.00  res_num_in_passive:                     0
% 2.13/1.00  res_num_in_active:                      0
% 2.13/1.00  res_num_of_loops:                       171
% 2.13/1.00  res_forward_subset_subsumed:            2
% 2.13/1.00  res_backward_subset_subsumed:           0
% 2.13/1.00  res_forward_subsumed:                   0
% 2.13/1.00  res_backward_subsumed:                  0
% 2.13/1.00  res_forward_subsumption_resolution:     0
% 2.13/1.00  res_backward_subsumption_resolution:    0
% 2.13/1.00  res_clause_to_clause_subsumption:       65
% 2.13/1.00  res_orphan_elimination:                 0
% 2.13/1.00  res_tautology_del:                      14
% 2.13/1.00  res_num_eq_res_simplified:              0
% 2.13/1.00  res_num_sel_changes:                    0
% 2.13/1.00  res_moves_from_active_to_pass:          0
% 2.13/1.00  
% 2.13/1.00  ------ Superposition
% 2.13/1.00  
% 2.13/1.00  sup_time_total:                         0.
% 2.13/1.00  sup_time_generating:                    0.
% 2.13/1.00  sup_time_sim_full:                      0.
% 2.13/1.00  sup_time_sim_immed:                     0.
% 2.13/1.00  
% 2.13/1.00  sup_num_of_clauses:                     0
% 2.13/1.00  sup_num_in_active:                      0
% 2.13/1.00  sup_num_in_passive:                     0
% 2.13/1.00  sup_num_of_loops:                       0
% 2.13/1.00  sup_fw_superposition:                   0
% 2.13/1.00  sup_bw_superposition:                   0
% 2.13/1.00  sup_immediate_simplified:               0
% 2.13/1.00  sup_given_eliminated:                   0
% 2.13/1.00  comparisons_done:                       0
% 2.13/1.00  comparisons_avoided:                    0
% 2.13/1.00  
% 2.13/1.00  ------ Simplifications
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  sim_fw_subset_subsumed:                 0
% 2.13/1.00  sim_bw_subset_subsumed:                 2
% 2.13/1.00  sim_fw_subsumed:                        0
% 2.13/1.00  sim_bw_subsumed:                        4
% 2.13/1.00  sim_fw_subsumption_res:                 3
% 2.13/1.00  sim_bw_subsumption_res:                 0
% 2.13/1.00  sim_tautology_del:                      0
% 2.13/1.00  sim_eq_tautology_del:                   1
% 2.13/1.00  sim_eq_res_simp:                        2
% 2.13/1.00  sim_fw_demodulated:                     0
% 2.13/1.00  sim_bw_demodulated:                     5
% 2.13/1.00  sim_light_normalised:                   6
% 2.13/1.00  sim_joinable_taut:                      0
% 2.13/1.00  sim_joinable_simp:                      0
% 2.13/1.00  sim_ac_normalised:                      0
% 2.13/1.00  sim_smt_subsumption:                    0
% 2.13/1.00  
%------------------------------------------------------------------------------
